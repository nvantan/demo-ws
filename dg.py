"""
Xelis Mining Client Implementation

This module implements a Stratum mining client for the Xelis cryptocurrency.
It handles connection to mining pools, job management, and proof-of-work calculations.
"""

from __future__ import print_function

# Standard library imports
import os
import sys
import time
import json
import random
import struct
import hashlib
import binascii
import threading
import multiprocessing
from re import S as AD
from concurrent.futures import ThreadPoolExecutor

# Third-party imports
import websocket

# Constants for Stratum protocol messages and parameters
SHARED = 'shared'  # Key for shared data in message queue
HASHRATE = 'hashrate'  # Key for hashrate reporting
MAX_NONCE = 'max_nonce'  # Maximum nonce value for mining
EXTRANONCE2_SIZE = 'extranonce2_size'  # Size of extranonce2 in bytes
EXTRANONCE1 = 'extranonce1'  # First part of extranonce
TARGET = 'target'  # Mining target difficulty
NBITS = 'nbits'  # Network difficulty bits
VERSION = 'version'  # Block version
MERKLE_BRANCHES = 'merkle_branches'  # Merkle tree branches
COINB2 = 'coinb2'  # Second part of coinbase transaction
COINB1 = 'coinb1'  # First part of coinbase transaction
PREVHASH = 'prevhash'  # Previous block hash
HEX_FORMAT = '%064x'  # Format for hex string padding
FALSE = False
PORT = 'port'  # Mining pool port
PRINT_FUNC = print
TUPLE_TYPE = tuple
VALUE_ERROR = ValueError
MINING_SUBMIT = 'mining.submit'  # Stratum submit message
MINING_SUBSCRIBE = 'mining.subscribe'  # Stratum subscribe message
NTIME = 'ntime'  # Block timestamp
JOB_ID = 'job_id'  # Mining job identifier
THREADS = 'threads'  # Number of mining threads
RANGE_FUNC = range
ISINSTANCE_FUNC = isinstance
EXCEPTION_TYPE = Exception
NEWLINE = '\n'
LEN_FUNC = len
PARAMS = 'params'  # Message parameters
METHOD = 'method'  # Message method
ID = 'id'  # Message identifier
TRUE = True
INT_FUNC = int
NONE = None
PROPERTY_DECORATOR = property

# Add libs directory to path for custom hash implementations
LIBS_PATH = os.path.abspath('./libs')
sys.path.append(LIBS_PATH)

# Algorithm configuration
ALGORITHM_NAME = 'xelisv2_pepew'  # Mining algorithm name
SUPPORTED_ALGORITHMS = [ALGORITHM_NAME]  # List of supported algorithms

def load_config(file_path):
    """
    Load mining configuration from a file.
    
    Args:
        file_path (str): Path to the configuration file
        
    Returns:
        dict: Configuration parameters including:
            - proxy: WebSocket proxy URL
            - host: Mining pool host
            - port: Mining pool port
            - username: Mining worker username
            - password: Mining worker password
            - threads: Number of mining threads
    """
    config = {}
    with open(file_path, 'r') as file:
        for line in file:
            key, value = line.strip().split('=', 1)
            if key == PORT:
                value = INT_FUNC(value)
            elif key == THREADS:
                if value.startswith('['):
                    value = json.loads(value)
                else:
                    value = INT_FUNC(value)
            config[key] = value
    return config

def format_hashrate(hashrate):
    """
    Format hashrate into human-readable format.
    
    Args:
        hashrate (float): Hashrate in hashes per second
        
    Returns:
        str: Formatted hashrate string (e.g., "1.23 MH/s")
    """
    if hashrate < 1000:
        return f'{hashrate:.2f} B/s'
    if hashrate < 10000000:
        return f'{hashrate/1000:.2f} KB/s'
    if hashrate < 10000000000:
        return f'{hashrate/1000000:.2f} MB/s'
    return f'{hashrate/1000000000:.2f} GB/s'

class MiningJob:
    """
    Represents a mining job with all necessary parameters for block mining.
    
    This class handles the core mining logic including:
    - Merkle root calculation
    - Block header construction
    - Nonce iteration
    - Proof-of-work verification
    """
    
    def __init__(self, job_id, prevhash, coinb1, coinb2, merkle_branches, version, 
                 nbits, ntime, target, extranonce1, extranonce2_size, proof_of_work, 
                 max_nonce=4294967295):
        """
        Initialize a new mining job.
        
        Args:
            job_id (str): Unique identifier for the mining job
            prevhash (str): Previous block hash
            coinb1 (str): First part of coinbase transaction
            coinb2 (str): Second part of coinbase transaction
            merkle_branches (list): Merkle tree branches
            version (str): Block version
            nbits (str): Network difficulty bits
            ntime (str): Block timestamp
            target (str): Mining target difficulty
            extranonce1 (str): First part of extranonce
            extranonce2_size (int): Size of extranonce2 in bytes
            proof_of_work (callable): Function to calculate proof-of-work hash
            max_nonce (int): Maximum nonce value for mining
        """
        self._job_id = job_id
        self._prevhash = prevhash
        self._coinb1 = coinb1
        self._coinb2 = coinb2
        self._merkle_branches = [branch for branch in merkle_branches]
        self._version = version
        self._nbits = nbits
        self._ntime = ntime
        self._max_nonce = max_nonce
        self._target = target
        self._extranonce1 = extranonce1
        self._extranonce2_size = extranonce2_size
        self._proof_of_work = proof_of_work
        self._done = FALSE
        self._dt = 0.0
        self._hash_count = 0

    # Properties for accessing job parameters
    id = PROPERTY_DECORATOR(lambda s: s._job_id)
    prevhash = PROPERTY_DECORATOR(lambda s: s._prevhash)
    coinb1 = PROPERTY_DECORATOR(lambda s: s._coinb1)
    coinb2 = PROPERTY_DECORATOR(lambda s: s._coinb2)
    merkle_branches = PROPERTY_DECORATOR(lambda s: [branch for branch in s._merkle_branches])
    version = PROPERTY_DECORATOR(lambda s: s._version)
    nbits = PROPERTY_DECORATOR(lambda s: s._nbits)
    ntime = PROPERTY_DECORATOR(lambda s: s._ntime)
    target = PROPERTY_DECORATOR(lambda s: s._target)
    extranonce1 = PROPERTY_DECORATOR(lambda s: s._extranonce1)
    extranonce2_size = PROPERTY_DECORATOR(lambda s: s._extranonce2_size)
    proof_of_work = PROPERTY_DECORATOR(lambda s: s._proof_of_work)

    @PROPERTY_DECORATOR
    def hashrate(self):
        """
        Calculate current hashrate based on hash count and elapsed time.
        
        Returns:
            float: Current hashrate in hashes per second
        """
        if self._dt == 0:
            return 0.0
        return self._hash_count / self._dt

    def merkle_root_bin(self, extranonce2_bin):
        """
        Calculate merkle root in binary format.
        
        Args:
            extranonce2_bin (bytes): Binary extranonce2 value
            
        Returns:
            bytes: Binary merkle root hash
        """
        # Construct coinbase transaction
        coinbase = binascii.unhexlify(self._coinb1) + \
                  binascii.unhexlify(self._extranonce1) + \
                  extranonce2_bin + \
                  binascii.unhexlify(self._coinb2)
        
        # Calculate initial merkle root
        merkle_root = hashlib.sha256(hashlib.sha256(coinbase).digest()).digest()
        
        # Add merkle branches
        for branch in self._merkle_branches:
            merkle_root = hashlib.sha256(hashlib.sha256(merkle_root + 
                                                       binascii.unhexlify(branch)).digest()).digest()
        return merkle_root

    def stop(self):
        """Stop the mining process."""
        self._done = TRUE

    def mine(self, nonce_start=0, nonce_end=1, callback=NONE):
        """
        Execute mining process for the given nonce range.
        
        Args:
            nonce_start (int): Starting nonce value
            nonce_end (int): Ending nonce value
            callback (callable): Function to call when a share is found
        """
        start_time = time.time()
        
        # Generate random extranonce2
        extranonce2 = '{:0{}x}'.format(
            random.randint(0, 2**(8 * self.extranonce2_size) - 1),
            self.extranonce2_size * 2
        )
        extranonce2_bin = (struct.pack('<I', INT_FUNC(extranonce2, 16)) 
                          if self.extranonce2_size <= 4 
                          else struct.pack('<Q', INT_FUNC(extranonce2, 16)))
        
        # Calculate merkle root and construct block header
        merkle_root = self.merkle_root_bin(extranonce2_bin)
        header = (struct.pack('<I', INT_FUNC(self._version)) +
                 binascii.unhexlify(self._prevhash)[::-1] +
                 merkle_root +
                 struct.pack('<I', INT_FUNC(self._ntime)) +
                 struct.pack('<I', INT_FUNC(self._nbits)))

        # Iterate through nonce range
        for nonce in RANGE_FUNC(nonce_start, nonce_end, 1):
            if self._done:
                self._dt += time.time() - start_time
                raise StopIteration

            # Calculate proof-of-work hash
            nonce_bin = struct.pack('<I', nonce)
            pow_hash = binascii.hexlify(
                self.proof_of_work(header + nonce_bin)[::-1]
            ).decode('utf-8')

            # Check if share meets target difficulty
            if INT_FUNC(pow_hash, 16) <= INT_FUNC(self.target, 16):
                result = {
                    JOB_ID: self.id,
                    'extranonce2': binascii.hexlify(extranonce2_bin),
                    NTIME: str(self._ntime),
                    'nonce': binascii.hexlify(nonce_bin[::-1])
                }
                self._dt += time.time() - start_time
                start_time = time.time()
                
                if callback is not NONE:
                    callback(result, self.hashrate)

            self._hash_count += 1

    def __str__(self):
        """String representation of the mining job."""
        return (f'<Job id={self.id} prevhash={self.prevhash} '
                f'coinb1={self.coinb1} coinb2={self.coinb2} '
                f'merkle_branches={self.merkle_branches} '
                f'version={self.version} nbits={self.nbits} '
                f'ntime={self.ntime} target={self.target} '
                f'extranonce1={self.extranonce1} '
                f'extranonce2_size={self.extranonce2_size}>')

class Subscription:
    _max_nonce = None

    def ProofOfWork(self):
        raise Exception("Do not use the Subscription class directly, subclass it")

    class StateException(Exception):
        pass

    def __init__(self):
        self._id = None
        self._difficulty = None
        self._extranonce1 = None
        self._extranonce2_size = None
        self._target = None
        self._worker_name = None
        self._mining_thread = None

    id = PROPERTY_DECORATOR(lambda s: s._id)
    worker_name = PROPERTY_DECORATOR(lambda s: s._worker_name)
    difficulty = PROPERTY_DECORATOR(lambda s: s._difficulty)
    target = PROPERTY_DECORATOR(lambda s: s._target)
    extranonce1 = PROPERTY_DECORATOR(lambda s: s._extranonce1)
    extranonce2_size = PROPERTY_DECORATOR(lambda s: s._extranonce2_size)

    def set_worker_name(self, worker_name):
        if self._worker_name:
            raise self.StateException("Already authenticated as %r (requesting %r)" % (self._worker_name, worker_name))
        self._worker_name = worker_name

    def _set_target(self, target):
        self._target = target

    def set_difficulty(self, difficulty):
        if difficulty < 0:
            raise self.StateException("Difficulty must be non-negative")
        self._difficulty = difficulty
        self._set_target(self._difficulty)

    def set_subscription(self, subscription_id, extranonce1, extranonce2_size):
        if self._id is None:
            raise self.StateException("Already subscribed")
        self._id = subscription_id
        self._extranonce1 = extranonce1
        self._extranonce2_size = extranonce2_size

    def create_job(self, job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime):
        if self._id is None:
            raise self.StateException("Not subscribed")
        return MiningJob(job_id=job_id, prevhash=prevhash, coinb1=coinb1, coinb2=coinb2, merkle_branches=merkle_branches, version=version, nbits=nbits, ntime=ntime, target=self.target, extranonce1=self.extranonce1, extranonce2_size=self.extranonce2_size, proof_of_work=self.ProofOfWork, max_nonce=self._max_nonce)

    def __str__(self):
        return "<Subscription id=%s, extranonce1=%s, extranonce2_size=%d, difficulty=%d worker_name=%s>" % (self.id, self.extranonce1, self.extranonce2_size, self.difficulty, self.worker_name)

class Miner(Subscription):
    import v3.xelisv2_hash as hash_module
    ProofOfWork = hash_module.getPoWHash
    _max_nonce = 4294967295

    def _set_target(self, target):
        self._target = target

class MinerPool:
    def __init__(self, proxy, pool_host, pool_port, username, password, threads=4, algorithm=ALGORITHM_NAME):
        self._proxy = proxy
        self._pool_host = pool_host
        self._pool_port = pool_port
        self._username = username
        self._password = password
        self._threads_range = threads if isinstance(threads, (list, tuple)) else None
        self._threads = threads[0] if isinstance(threads, (list, tuple)) else threads
        self._subscription = MinerPool.get_algorithm(algorithm)()
        self._job = []
        self._ws = None
        self._main_thread = None
        self._accepted_shares = 0
        self._accepted_hash = 0
        self._queue = multiprocessing.Queue()
        self._processes = []
        self._hashrates = []
        self._current_diff = 0
        self._current_job_id = 'N/A'
        self._current_job = None
        self._last_submit_time = 0
        self.job_manager = multiprocessing.Manager().dict()

        self._proxy = PROPERTY_DECORATOR(lambda s: s._proxy)
        self._pool_host = PROPERTY_DECORATOR(lambda s: s._pool_host)
        self._pool_port = PROPERTY_DECORATOR(lambda s: s._pool_port)
        self._username = PROPERTY_DECORATOR(lambda s: s._username)
        self._password = PROPERTY_DECORATOR(lambda s: s._password)
        self._threads = PROPERTY_DECORATOR(lambda s: s._threads)
        self._current_diff = PROPERTY_DECORATOR(lambda s: s._current_diff)

    def _set_threads(self):
        if self._threads_range is not None:
            self._threads = random.randint(self._threads_range[0], self._threads_range[1])

    def _console_log(self, hashrate, shared):
        os.system('clear')
        print("🟢　%s　|　⚙️　%s　|　🔀　%d　|　✅　%d　|　🚀　%s" % ('ACTIVE', self._current_job_id, self.threads, shared, format_hashrate(hashrate)))

    def _spawn_job_thread(self, job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime):
        return self._subscription.create_job(job_id=job_id, prevhash=prevhash, coinb1=coinb1, coinb2=coinb2, merkle_branches=merkle_branches, version=version, nbits=nbits, ntime=ntime)

    def run(self, shared_data, nonce_start, nonce_end, callback):
        self._current_job = shared_data
        self._current_job_id = shared_data.id
        self._console_log(self._accepted_hash, self._accepted_shares)

        def hash_callback(result, hashrate):
            callback(result, hashrate * self.threads)

        def job_thread(job, nonce_start, nonce_end, submit):
            try:
                job.mine(nonce_start=nonce_start, nonce_end=nonce_end, callback=submit)
            except Exception as e:
                print(e)

        for i in range(self.threads):
            nonce_start_i = nonce_start + i * self._subscription._max_nonce // self.threads
            nonce_end_i = nonce_start_i + (self._subscription._max_nonce // self.threads) - 1
            process = multiprocessing.Process(target=self.run, args=(self.job_manager, nonce_start_i, nonce_end_i, hash_callback), daemon=True)
            process.start()
            self._processes.append(process)

    def queue_message(self):
        while True:
            if not self._queue.empty():
                job = self._queue.get()
                self._accepted_hash = job[HASHRATE]
                self._ws.send(job[SHARED])
            else:
                time.sleep(0.25)

    def on_open(self, ws):
        subscribe_message = {
            METHOD: MINING_SUBSCRIBE,
            PARAMS: ['python-pepepow/3.0']
        }
        ws.send(json.dumps(subscribe_message) + NEWLINE)
        self._console_log(0, 0)
        self._ws = ws
        self._console_log(0, 0)

        def submit_callback(shared, hashrate):
            self._queue.put({SHARED: json.dumps(shared) + NEWLINE, HASHRATE: hashrate})

        for i in range(self.threads):
            nonce_start_i = i * self._subscription._max_nonce // self.threads
            nonce_end_i = (i + 1) * self._subscription._max_nonce // self.threads - 1
            process = multiprocessing.Process(target=self.run, args=(self.job_manager, nonce_start_i, nonce_end_i, submit_callback), daemon=True)
            process.start()

    def handle_message(self, ws, message):
        try:
            self.on_message(ws, message)
        except Exception as e:
            print(e)

    def on_message(self, ws, message):
        R = 'mining.extranonce.subscribe'
        Q = 'mining.authorize'
        S = message.split(NEWLINE)
        for T in S:
            if not T.strip():
                continue
            I = json.loads(T)
            D = I.get(METHOD) or I.get(ID)
            H = I.get(PARAMS) or I.get('result')
            W = I.get('error') or FALSE
            if D == MINING_SUBMIT:
                self._last_submit_time = int(time.time() * 1000)
                if W is FALSE:
                    self._accepted_shares += 1
                    print("Accepted shares: %d" % self._accepted_shares)
                    self._console_log(self._accepted_hash, self._accepted_shares)
            elif D == Q:
                self._subscription.set_worker_name(self.username)
            elif D == 'mining.set_difficulty':
                O, = H
                self._current_diff = O
                self._subscription.set_difficulty(O)
                print("Change difficulty: difficulty=%s" % O)
            elif D == MINING_SUBSCRIBE:
                (n, U), X, Y = H
                self._subscription.set_subscription(U, X, Y)
                print("Subscribed: subscription_id=%s" % U)
                d = {METHOD: R, PARAMS: []}
                ws.send(json.dumps(d) + NEWLINE)
                e = {METHOD: Q, PARAMS: [self.username, self.password]}
                ws.send(json.dumps(e) + NEWLINE)
            elif D == 'mining.notify':
                if len(H) != 9:
                    raise Exception("Malformed mining.notify message")
                P, f, g, h, i, j, k, l, m = H
                print("New job: %s" % P)
                self._current_job_id = P
                self._console_log(self._accepted_hash, self._accepted_shares)
                self.job_manager.update({JOB_ID: P, 'q': f, 'r': g, 's': h, 't': i, 'u': j, 'v': k, 'a': l, 'clean_jobs': m, 'w': self._subscription.target, 'x': self._subscription.extranonce1, 'y': self._subscription.extranonce2_size, 'z': 4294967295})
            elif D == R:
                print("Extranonce Subscribe: %s" % H)

    def on_error(self, ws, msg):
        print(msg)

    def on_close(self, b):
        print("WebSocket closed")

    def serve_forever(self):
        websocket.enableTrace(TRUE)
        self._ws = websocket.WebSocketApp(self.proxy, on_open=self.on_open, on_message=self.handle_message, on_error=self.on_error, on_close=self.on_close)
        self._console_log(0, 0)
        self._ws.run_forever()

if __name__ == '__main__':
    D = load_config('data.txt')
    P = sys.argv[1] if len(sys.argv) > 1 else None
    if P:
        if ',' in P:
            D[THREADS] = json.loads('[{}]'.format(P))
        else:
            D[THREADS] = INT_FUNC(P)
    AC = MinerPool(D['proxy'], D['host'], D[PORT], D['username'], D['password'], D[THREADS], ALGORITHM_NAME)
    AC.serve_forever()
