"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.StratumConnection = exports.StratumProxyServer = void 0;
var net = require("net");
var fs = require("fs");
var ws_1 = require("ws");
var http = require("http");
var CONFIG = {
    PROXY_PORT: 8080,
    STRATUM_HOST: "xelisv2-pepew.na.mine.zpool.ca",
    STRATUM_PORT: 4833,
    RECONNECT_DELAY: 5000,
    TIMEOUT: 30000
};
var StratumProxyServer = /** @class */ (function () {
    function StratumProxyServer(port) {
        if (port === void 0) { port = CONFIG.PROXY_PORT; }
        this.pythonClients = new Map();
        this.connectionCounter = 0;
        this.port = port;
        this.httpServer = http.createServer();
        this.wsServer = new ws_1.WebSocketServer({ server: this.httpServer });
        this.setupWebSocketServer();
    }
    StratumProxyServer.prototype.setupWebSocketServer = function () {
        var _this = this;
        this.wsServer.on('connection', function (ws, req) {
            var clientId = ++_this.connectionCounter;
            var clientAddress = req.socket.remoteAddress;
            console.log("\uD83D\uDD17 Python client ".concat(clientId, " connected from ").concat(clientAddress));
            // Create a dedicated Stratum connection for this client
            var stratumConnection = new StratumConnection(clientId, ws);
            _this.pythonClients.set(ws, stratumConnection);
            // Handle messages from Python client
            ws.on('message', function (data) {
                var message = data.toString().trim();
                if (message) {
                    console.log("\uD83D\uDCE8 [Client ".concat(clientId, "] Received: ").concat(message));
                    stratumConnection.sendToStratum(message);
                }
            });
            ws.on('close', function () {
                console.log("\uD83D\uDD0C Python client ".concat(clientId, " disconnected"));
                stratumConnection.disconnect();
                _this.pythonClients.delete(ws);
            });
            ws.on('error', function (error) {
                console.error("\u274C [Client ".concat(clientId, "] WebSocket error:"), error);
                stratumConnection.disconnect();
                _this.pythonClients.delete(ws);
            });
            // Connect to Stratum pool when client connects
            stratumConnection.connectToStratum();
        });
    };
    StratumProxyServer.prototype.start = function () {
        var _this = this;
        this.httpServer.listen(this.port, function () {
            console.log("\uD83D\uDE80 Stratum Proxy Server listening on port ".concat(_this.port));
            console.log("\uD83D\uDCE1 Python clients can connect to: ws://localhost:".concat(_this.port));
            console.log("\uD83C\uDFAF Forwarding to Stratum pool: ".concat(CONFIG.STRATUM_HOST, ":").concat(CONFIG.STRATUM_PORT));
            console.log("\u23F3 Waiting for Python clients to connect...");
        });
    };
    StratumProxyServer.prototype.stop = function () {
        console.log('🛑 Shutting down proxy server...');
        this.pythonClients.forEach(function (stratumConnection) {
            stratumConnection.disconnect();
        });
        this.wsServer.close();
        this.httpServer.close();
    };
    return StratumProxyServer;
}());
exports.StratumProxyServer = StratumProxyServer;
var StratumConnection = /** @class */ (function () {
    function StratumConnection(clientId, pythonClient) {
        this.stratumSocket = null;
        this.isConnected = false;
        this.reconnectAttempts = 0;
        this.maxReconnectAttempts = 5;
        this.messageQueue = [];
        this.clientId = clientId;
        this.pythonClient = pythonClient;
    }
    StratumConnection.prototype.connectToStratum = function () {
        if (this.isConnected) {
            console.log("\u26A0\uFE0F  [Client ".concat(this.clientId, "] Already connected to Stratum pool"));
            return;
        }
        console.log("\uD83D\uDD04 [Client ".concat(this.clientId, "] Connecting to Stratum pool..."));
        this.stratumSocket = new net.Socket();
        this.setupStratumEventHandlers();
        this.stratumSocket.connect({
            port: CONFIG.STRATUM_PORT,
            host: CONFIG.STRATUM_HOST
        });
        this.stratumSocket.setTimeout(CONFIG.TIMEOUT);
    };
    StratumConnection.prototype.setupStratumEventHandlers = function () {
        var _this = this;
        if (!this.stratumSocket)
            return;
        this.stratumSocket.on('connect', function () {
            console.log("\u2705 [Client ".concat(_this.clientId, "] Connected to Stratum pool"));
            _this.isConnected = true;
            _this.reconnectAttempts = 0;
            _this.processMessageQueue();
        });
        this.stratumSocket.on('data', function (data) {
            var messages = data.toString().split('\n').filter(function (msg) { return msg.trim(); });
            for (var _i = 0, messages_1 = messages; _i < messages_1.length; _i++) {
                var message = messages_1[_i];
                if (message.trim()) {
                    console.log("\uD83D\uDCE4 [Client ".concat(_this.clientId, "] Forwarding to Python: ").concat(message));
                    _this.sendToPython(message);
                }
            }
        });
        this.stratumSocket.on('close', function () {
            console.log("\uD83D\uDD0C [Client ".concat(_this.clientId, "] Stratum connection closed"));
            _this.isConnected = false;
            _this.attemptReconnect();
        });
        this.stratumSocket.on('error', function (error) {
            console.error("\u274C [Client ".concat(_this.clientId, "] Stratum connection error:"), error.message);
            _this.isConnected = false;
        });
        this.stratumSocket.on('timeout', function () {
            console.log("\u23F0 [Client ".concat(_this.clientId, "] Stratum connection timeout"));
            if (_this.stratumSocket) {
                _this.stratumSocket.destroy();
            }
        });
    };
    StratumConnection.prototype.sendToStratum = function (message) {
        if (!message.endsWith('\n')) {
            message += '\n';
        }
        if (this.isConnected && this.stratumSocket) {
            console.log("\uD83D\uDCE4 [Client ".concat(this.clientId, "] Forwarding to Stratum: ").concat(message.trim()));
            this.stratumSocket.write(message);
        }
        else {
            console.log("\u26A0\uFE0F  [Client ".concat(this.clientId, "] Stratum not connected, queuing message"));
            this.messageQueue.push(message);
        }
    };
    StratumConnection.prototype.sendToPython = function (message) {
        if (this.pythonClient.readyState === ws_1.WebSocket.OPEN) {
            this.pythonClient.send(message);
        }
    };
    StratumConnection.prototype.processMessageQueue = function () {
        while (this.messageQueue.length > 0) {
            var message = this.messageQueue.shift();
            if (message && this.stratumSocket) {
                console.log("\uD83D\uDCE4 [Client ".concat(this.clientId, "] Processing queued message: ").concat(message.trim()));
                this.stratumSocket.write(message);
            }
        }
    };
    StratumConnection.prototype.attemptReconnect = function () {
        var _this = this;
        if (this.reconnectAttempts < this.maxReconnectAttempts) {
            this.reconnectAttempts++;
            console.log("\uD83D\uDD04 [Client ".concat(this.clientId, "] Attempting to reconnect (").concat(this.reconnectAttempts, "/").concat(this.maxReconnectAttempts, ") in ").concat(CONFIG.RECONNECT_DELAY / 1000, "s..."));
            setTimeout(function () {
                _this.connectToStratum();
            }, CONFIG.RECONNECT_DELAY);
        }
        else {
            console.log("\u274C [Client ".concat(this.clientId, "] Max reconnection attempts reached"));
        }
    };
    StratumConnection.prototype.disconnect = function () {
        if (this.stratumSocket) {
            console.log("\uD83D\uDD1A [Client ".concat(this.clientId, "] Disconnecting from Stratum pool"));
            this.stratumSocket.end();
            this.stratumSocket = null;
        }
        this.isConnected = false;
    };
    return StratumConnection;
}());
exports.StratumConnection = StratumConnection;
// Configuration loader for data.txt compatibility
var ConfigLoader = /** @class */ (function () {
    function ConfigLoader() {
    }
    ConfigLoader.loadConfig = function (filePath) {
        if (filePath === void 0) { filePath = 'data.txt'; }
        var config = {};
        try {
            var data = fs.readFileSync(filePath, 'utf-8');
            var lines = data.split('\n');
            for (var _i = 0, lines_1 = lines; _i < lines_1.length; _i++) {
                var line = lines_1[_i];
                var trimmed = line.trim();
                if (trimmed && trimmed.includes('=')) {
                    var _a = trimmed.split('=', 2), key = _a[0], value = _a[1];
                    if (key === 'port') {
                        config[key] = parseInt(value);
                    }
                    else if (key === 'threads') {
                        if (value.startsWith('[')) {
                            config[key] = JSON.parse(value);
                        }
                        else {
                            config[key] = parseInt(value);
                        }
                    }
                    else {
                        config[key] = value;
                    }
                }
            }
            console.log("✅ Configuration loaded:", config);
            return config;
        }
        catch (error) {
            console.log("⚠️  Could not load config file, using defaults");
            return {};
        }
    };
    return ConfigLoader;
}());
// Main execution
console.log("🚀 Starting Stratum Proxy Server for Python Mining Client");
console.log("📖 This proxy server will:");
console.log("   1. Listen for WebSocket connections from Python mining client");
console.log("   2. Connect to actual Stratum pool when client connects");
console.log("   3. Forward messages bidirectionally between client and pool");
console.log("   4. Handle reconnections and error recovery");
console.log("");
var proxyServer = new StratumProxyServer();
proxyServer.start();
// Graceful shutdown
process.on('SIGINT', function () {
    console.log('\n🛑 Shutting down gracefully...');
    proxyServer.stop();
    process.exit(0);
});
process.on('SIGTERM', function () {
    console.log('\n🛑 Received SIGTERM, shutting down...');
    proxyServer.stop();
    process.exit(0);
});
// Keep the process alive
process.stdin.resume();
