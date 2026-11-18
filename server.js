'use strict';

const express = require('express');
const http = require('node:http');
const path = require('node:path');
const fs = require('node:fs');
const os = require('node:os');
const { randomUUID } = require('node:crypto');
const { Server } = require('socket.io');
const THREE = require('three');

function createGameServer(options = {}) {
  const root = options.root || __dirname;
  const html = fs.readFileSync(path.join(root, 'index.html'), 'utf8');
  const match = html.match(/<script id="lan-manifest" type="application\/json">([\s\S]*?)<\/script>/);
  if (!match) throw new Error('Falta lan-manifest en index.html. Usa los dos archivos de la misma versión.');
  const manifest = JSON.parse(match[1]);
  const clamp = (n, a, b) => Math.max(a, Math.min(b, n));
  const mod = (n, m) => ((n % m) + m) % m;
  const diffAngle = (a, b) => mod(a - b + Math.PI, Math.PI * 2) - Math.PI;
  const app = express();
  app.disable('x-powered-by');
  app.get(['/', '/index.html'], (req, res) => res.sendFile(path.join(root, 'index.html')));
  app.get('/health', (req, res) => res.json({ ok: true, players: players.size, revision: room.revision }));
  app.use('/vendor', express.static(path.join(path.dirname(require.resolve('three')), '.'), {
    dotfiles: 'deny', index: false, maxAge: '1d'
  }));
  app.use((req, res) => res.status(404).type('text').send('No encontrado'));
  const server = http.createServer(app);
  const io = new Server(server, {
    serveClient: true, maxHttpBufferSize: 16384,
    pingInterval: 1500, pingTimeout: 3500,
    transports: ['websocket', 'polling'], perMessageDeflate: false
  });
  const tracks = manifest.courses.map(course => {
    const curve = new THREE.CatmullRomCurve3(course.points.map(p => new THREE.Vector3(...p)), true, 'catmullrom', .42);
    curve.arcLengthDivisions = 2400;
    const length = curve.getLength();
    const samples = Array.from({ length: 800 }, (_, i) => {
      const p = curve.getPointAt(i / 800), t = curve.getTangentAt(i / 800), l = Math.hypot(t.x, t.z);
      return { x: p.x, y: p.y, z: p.z, tx: t.x / l, tz: t.z / l, nx: t.z / l, nz: -t.x / l };
    });
    return { ...course, curve, length, samples };
  });
  const players = new Map(), shots = new Map();
  const room = { revision: 1, course: 0, cc: 100, phase: 'lobby', startsAt: 0, firstFinish: 0 };
  const boxes = Array(12).fill(0);
  const itemCounts = { mushroom: 1, triple: 3, green: 1, red: 1, banana: 1, tripleBanana: 3, lightning: 1, star: 1 };
  const MAX_PLAYERS = 12;
  let shotSequence = 0, closed = false;
  const track = () => tracks[room.course];
  const along = (a, b) => mod(a - b + track().length / 2, track().length) - track().length / 2;

  function sample(s) {
    const t = track(), v = mod(s, t.length) / t.length * 800, i = Math.floor(v), f = v - i;
    const a = t.samples[i], b = t.samples[(i + 1) % 800];
    const tx = a.tx + (b.tx - a.tx) * f, tz = a.tz + (b.tz - a.tz) * f, n = Math.hypot(tx, tz);
    return { x: a.x + (b.x - a.x) * f, y: a.y + (b.y - a.y) * f, z: a.z + (b.z - a.z) * f, tx: tx / n, tz: tz / n, nx: tz / n, nz: -tx / n, s: mod(s, t.length) };
  }
  function nearest(x, z, hint) {
    const t = track(), step = t.length / 800, center = Math.floor(mod(hint, t.length) / step);
    let best = Infinity, bestS = hint;
    for (let j = -25; j <= 25; j++) {
      const i = mod(center + j, 800), a = t.samples[i], b = t.samples[(i + 1) % 800];
      const dx = b.x - a.x, dz = b.z - a.z;
      const f = clamp(((x - a.x) * dx + (z - a.z) * dz) / (dx * dx + dz * dz), 0, 1);
      const distance = (x - a.x - dx * f) ** 2 + (z - a.z - dz * f) ** 2;
      if (distance < best) { best = distance; bestS = (i + f) * step; }
    }
    const p = sample(bestS);
    return { ...p, offset: (x - p.x) * p.nx + (z - p.z) * p.nz };
  }
  const active = () => [...players.values()].filter(p => p.active);
  function ranking() {
    return active().sort((a, b) => a.finishTime !== null && b.finishTime !== null ? a.finishTime - b.finishTime : a.finishTime !== null ? -1 : b.finishTime !== null ? 1 : b.state.distance - a.state.distance);
  }
  function safeName(value) {
    return Array.from(String(value || '').normalize('NFC').replace(/[\u0000-\u001f\u007f<>]/g, '').trim()).slice(0, 18).join('') || 'Piloto';
  }
  function profile(p) { return { id: p.id, name: p.name, character: p.character, active: p.active, slot: p.slot, finished: p.finishTime !== null, finishTime: p.finishTime, dnf: p.dnf }; }
  function pose(p, now = Date.now()) {
    return { ...profile(p), ...p.state, character: p.character, lap: Math.min(3, 1 + Math.floor(Math.max(0, p.state.distance) / track().length)),
      star: Math.max(0, (p.starUntil - now) / 1000), shrink: Math.max(0, (p.shrinkUntil - now) / 1000),
      heldType: p.holding ? p.item : null, heldCount: p.holding ? p.itemCount : 0,
      finished: p.finishTime !== null, finishTime: p.finishTime, dnf: p.dnf };
  }
  function roomState() { return { ...room, serverTime: Date.now(), players: [...players.values()].map(profile), boxes: [...boxes], trackLength: track().length }; }
  function broadcastRoom() { io.emit('room', roomState()); }
  function resetPlayer(p) {
    const s = -12 - Math.floor(p.slot / 2) * 8, q = sample(s), lane = (p.slot % 2 ? 1 : -1) * 4.2;
    p.state = { x: q.x + q.nx * lane, y: q.y, z: q.z + q.nz * lane, heading: Math.atan2(q.tx, q.tz), speed: 0, s: q.s, distance: s, hop: 0, ground: q.y, drift: false, driftDir: 0, driftCharge: 0, spin: 0, crush: 0, rescue: 0, boost: 0 };
    p.finishTime = null; p.dnf = false; p.seq = -1; p.lastPose = Date.now();
    p.item = null; p.itemCount = 0; p.itemReady = 0; p.holding = false;
    p.starUntil = p.shrinkUntil = p.invulnerableUntil = 0;
  }
  function resetRace() {
    room.revision++; room.firstFinish = 0; shots.clear(); boxes.fill(0);
    room.phase = active().length ? 'countdown' : 'lobby';
    room.startsAt = active().length ? Date.now() + 3600 : 0;
    active().forEach(resetPlayer); broadcastRoom();
  }
  function finishIfReady(now) {
    const list = active();
    if (!list.length) { room.phase = 'lobby'; room.startsAt = 0; room.firstFinish = 0; return; }
    if (room.phase !== 'racing') return;
    const allFinished = list.every(p => p.finishTime !== null);
    if (allFinished || room.firstFinish && now - room.firstFinish > 45000) {
      list.forEach(p => { if (p.finishTime === null) p.dnf = true; });
      room.phase = 'results'; broadcastRoom();
      io.emit('race:results', { revision: room.revision, serverTime: now, players: ranking().map(p => pose(p, now)) });
    }
  }
  function limit(p, key, max, seconds = 1) {
    const now = Date.now(), previous = p.limits[key];
    if (!previous || now - previous.at > seconds * 1000) { p.limits[key] = { at: now, n: 1 }; return true; }
    return ++previous.n <= max;
  }
  function validRevision(data) { return data && data.revision === room.revision; }
  function inventory(p) { io.to(p.socketId).emit('item:inventory', { revision: room.revision, item: p.item, count: p.itemCount, readyAt: p.itemReady }); }
  function consume(p) { p.itemCount--; if (p.itemCount <= 0) { p.item = null; p.itemCount = 0; p.holding = false; } inventory(p); }
  function damage(p, kind = 'spin') {
    const now = Date.now();
    if (!p.active || p.finishTime !== null || p.state.rescue || p.starUntil > now || p.invulnerableUntil > now) return false;
    p.invulnerableUntil = now + 1800; p.holding = false;
    io.emit('effect:hit', { revision: room.revision, target: p.id, kind, at: now });
    return true;
  }
  function chooseItem(p) {
    const place = ranking().indexOf(p), fraction = place / Math.max(1, active().length - 1);
    const pool = fraction < .25 ? ['banana', 'green', 'mushroom', 'tripleBanana', 'green'] : fraction < .65 ? ['red', 'green', 'mushroom', 'triple', 'banana', 'star'] : ['triple', 'star', 'lightning', 'red', 'tripleBanana'];
    return pool[Math.floor(Math.random() * pool.length)];
  }
  function spawnShot(p, type, forward) {
    const banana = type === 'banana' || type === 'tripleBanana', back = banana && !forward;
    const heading = p.state.heading + (back ? Math.PI : 0), distance = back ? 4.6 : 4.2;
    const x = p.state.x + Math.sin(heading) * distance, z = p.state.z + Math.cos(heading) * distance;
    const q = nearest(x, z, p.state.s), sorted = ranking(), ahead = sorted[sorted.indexOf(p) - 1];
    const shot = { id: ++shotSequence, owner: p.id, type: banana ? 'banana' : type, target: type === 'red' && ahead ? ahead.id : null,
      x, y: q.y + 1.1, z, s: q.s, heading, speed: banana ? forward ? 27 : 0 : 79,
      hop: banana && forward ? 2 : 0, vy: banana && forward ? 9 : 0, life: banana ? 38 : 14, age: 0, bounces: 0 };
    shots.set(shot.id, shot);
  }
  function updateShots(dt) {
    for (const shot of shots.values()) {
      shot.life -= dt; shot.age += dt;
      if (shot.life <= 0) { shots.delete(shot.id); continue; }
      const target = players.get(shot.target);
      if (shot.type === 'red' && target?.active && target.finishTime === null) {
        const close = Math.hypot(target.state.x - shot.x, target.state.z - shot.z) < 30;
        const aim = close ? target.state : sample(shot.s + Math.min(25, Math.abs(along(target.state.s, shot.s))));
        shot.heading += diffAngle(Math.atan2(aim.x - shot.x, aim.z - shot.z), shot.heading) * Math.min(1, dt * 9);
      }
      shot.x += Math.sin(shot.heading) * shot.speed * dt; shot.z += Math.cos(shot.heading) * shot.speed * dt;
      const q = nearest(shot.x, shot.z, shot.s), half = track().width / 2 - 1; shot.s = q.s;
      if (shot.type !== 'banana' && Math.abs(q.offset) > half) {
        const nx = q.nx * Math.sign(q.offset), nz = q.nz * Math.sign(q.offset), dx = Math.sin(shot.heading), dz = Math.cos(shot.heading), dot = dx * nx + dz * nz;
        shot.heading = Math.atan2(dx - 2 * dot * nx, dz - 2 * dot * nz);
        shot.x = q.x + q.nx * clamp(q.offset, -half, half); shot.z = q.z + q.nz * clamp(q.offset, -half, half);
        if (++shot.bounces > 12) { shots.delete(shot.id); continue; }
      }
      if (shot.type === 'banana' && (shot.hop > 0 || shot.vy > 0)) {
        shot.hop += shot.vy * dt; shot.vy -= 23 * dt;
        if (shot.hop <= 0) { shot.hop = 0; shot.vy = 0; shot.speed = 0; }
      }
      shot.y = q.y + 1.1 + shot.hop;
      for (const p of active()) {
        if (p.finishTime !== null || p.state.rescue || p.id === shot.owner && shot.age < .7 || Math.abs(p.state.y - shot.y) > 3) continue;
        let blocked = false;
        if (p.holding && p.itemCount) {
          const count = p.item === 'tripleBanana' ? p.itemCount : 1;
          for (let i = 0; i < count; i++) {
            const d = 4 + i * 2.7, x = p.state.x - Math.sin(p.state.heading) * d, z = p.state.z - Math.cos(p.state.heading) * d;
            if (Math.hypot(shot.x - x, shot.z - z) < 2.8) { consume(p); blocked = true; break; }
          }
        }
        if (blocked || Math.hypot(shot.x - p.state.x, shot.z - p.state.z) < (p.shrinkUntil > Date.now() ? 1.7 : 2.5)) {
          if (!blocked) damage(p);
          io.emit('effect:burst', { revision: room.revision, x: shot.x, y: shot.y, z: shot.z });
          shots.delete(shot.id); break;
        }
      }
    }
  }
  function removePlayer(p, disconnect = false) {
    if (!p) return;
    p.active = false; p.holding = false;
    for (const s of shots.values()) if (s.owner === p.id) shots.delete(s.id);
    if (disconnect) players.delete(p.id);
    io.emit('player:left', { id: p.id, revision: room.revision });
    finishIfReady(Date.now()); broadcastRoom();
  }
  io.on('connection', socket => {
    if (players.size >= 32) { socket.emit('notice', 'La sala está llena.'); socket.disconnect(true); return; }
    const p = { id: randomUUID(), socketId: socket.id, name: 'Piloto', character: 0, active: false, slot: -1, finishTime: null, dnf: false, state: {}, limits: {} };
    players.set(p.id, p);
    socket.emit('hello', { id: p.id, room: roomState(), maxPlayers: MAX_PLAYERS });
    broadcastRoom();
    const on = (event, handler) => socket.on(event, (data = {}, ack) => {
      const answer = typeof ack === 'function' ? ack : () => {};
      try { handler(data && typeof data === 'object' ? data : {}, answer); }
      catch (error) { console.error(event + ':', error.message); answer({ ok: false, error: 'No se ha podido procesar la acción.' }); }
    });
    on('clock:ping', (data, ack) => ack({ serverTime: Date.now() }));
    on('profile', (data, ack) => {
      if (!limit(p, 'profile', 8)) return ack({ ok: false, error: 'Espera un instante.' });
      if (typeof data.name === 'string') p.name = safeName(data.name);
      if (Number.isInteger(data.character) && data.character >= 0 && data.character < manifest.drivers) p.character = data.character;
      broadcastRoom(); ack({ ok: true, player: profile(p) });
    });
    on('join', (data, ack) => {
      if (!limit(p, 'join', 3)) return ack({ ok: false, error: 'Espera un instante.' });
      if (!p.active && active().length >= MAX_PLAYERS) return ack({ ok: false, error: 'La parrilla está completa (12 pilotos).' });
      p.name = safeName(data.name);
      if (Number.isInteger(data.character) && data.character >= 0 && data.character < manifest.drivers) p.character = data.character;
      if (!p.active) {
        const slots = new Set(active().map(p => p.slot)); p.slot = 0; while (slots.has(p.slot)) p.slot++;
        p.active = true; resetPlayer(p);
        if (room.phase === 'lobby' || room.phase === 'results') resetRace(); else broadcastRoom();
      }
      ack({ ok: true, id: p.id, room: roomState(), state: pose(p), item: p.item, count: p.itemCount });
    });
    on('leave', (data, ack) => { removePlayer(p); ack({ ok: true }); });
    on('room:settings', (data, ack) => {
      if (!limit(p, 'settings', 3, 2)) return ack({ ok: false, error: 'Espera antes de volver a cambiar la sala.' });
      if (!validRevision(data)) return ack({ ok: false, error: 'La sala ha cambiado. Vuelve a intentarlo.' });
      if (data.course !== undefined && (!Number.isInteger(data.course) || !tracks[data.course])) return ack({ ok: false, error: 'Circuito no válido.' });
      if (data.cc !== undefined && ![50, 100, 150].includes(data.cc)) return ack({ ok: false, error: 'Cilindrada no válida.' });
      if (data.course !== undefined) room.course = data.course;
      if (data.cc !== undefined) room.cc = data.cc;
      resetRace(); ack({ ok: true, room: roomState() });
    });
    on('pose', (data, ack) => {
      if (!p.active || !validRevision(data) || !limit(p, 'pose', 85) || !Number.isInteger(data.seq) || data.seq <= p.seq || !['countdown', 'racing'].includes(room.phase)) return;
      if (!['x', 'y', 'z', 'heading', 'speed'].every(k => Number.isFinite(data[k]))) return;
      if (Math.abs(data.x) > 5000 || Math.abs(data.z) > 5000 || data.y < -300 || data.y > 1000 || Math.abs(data.speed) > 140) return;
      const now = Date.now(), dt = clamp((now - p.lastPose) / 1000, .01, 2), rescuing = data.rescue > 0;
      const moved = Math.hypot(data.x - p.state.x, data.z - p.state.z);
      if (moved > 140 * dt + 12 && !rescuing && !p.state.rescue) { socket.emit('pose:correct', { revision: room.revision, state: pose(p) }); return; }
      if (room.phase === 'countdown') { if (moved > 3) socket.emit('pose:correct', { revision: room.revision, state: pose(p) }); return; }
      const q = nearest(data.x, data.z, p.state.s), ds = along(q.s, p.state.s);
      if (!rescuing && !p.state.rescue && Math.abs(ds) < 140 * dt + 15 && p.finishTime === null) p.state.distance += ds;
      if (rescuing && Number.isFinite(data.distance)) p.state.distance = Math.min(p.state.distance, data.distance);
      Object.assign(p.state, { x: data.x, y: data.y, z: data.z, heading: mod(data.heading + Math.PI, Math.PI * 2) - Math.PI, speed: data.speed, s: q.s,
        hop: clamp(Number(data.hop) || 0, 0, 30), ground: q.y, drift: !!data.drift, driftDir: Math.sign(Number(data.driftDir) || 0),
        driftCharge: clamp(Math.floor(Number(data.driftCharge) || 0), 0, 3), spin: clamp(Number(data.spin) || 0, 0, 2),
        crush: clamp(Number(data.crush) || 0, 0, 2), rescue: clamp(Number(data.rescue) || 0, 0, 3), boost: clamp(Number(data.boost) || 0, 0, 3) });
      p.seq = data.seq; p.lastPose = now;
      if (p.finishTime === null && p.state.distance >= track().length * 3) {
        p.finishTime = Math.max(0, (now - room.startsAt) / 1000);
        if (!room.firstFinish) room.firstFinish = now;
        io.emit('race:finish', { revision: room.revision, player: pose(p), at: now }); finishIfReady(now);
      }
    });
    on('box:claim', (data, ack) => {
      const now = Date.now();
      if (!p.active || p.finishTime !== null || !validRevision(data) || room.phase !== 'racing' || !limit(p, 'box', 8) || !Number.isInteger(data.box) || data.box < 0 || data.box >= 12 || p.item || boxes[data.box] > now) return ack({ ok: false });
      const s = [.065, .29, .53, .77][Math.floor(data.box / 3)] * track().length, lane = [-7, 0, 7][data.box % 3], q = sample(s);
      if (Math.hypot(p.state.x - q.x - q.nx * lane, p.state.z - q.z - q.nz * lane) > 7 || p.state.hop > 5) return ack({ ok: false });
      boxes[data.box] = now + 4500; p.item = chooseItem(p); p.itemCount = itemCounts[p.item]; p.itemReady = now + 1250;
      io.emit('box:update', { revision: room.revision, box: data.box, availableAt: boxes[data.box] });
      inventory(p); ack({ ok: true, item: p.item, count: p.itemCount, readyAt: p.itemReady });
    });
    on('item:hold', (data, ack) => {
      if (!p.active || !validRevision(data) || !limit(p, 'hold', 12) || !p.item || p.itemReady > Date.now()) return ack({ ok: false });
      p.holding = !!data.holding && ['green', 'red', 'banana', 'tripleBanana'].includes(p.item); ack({ ok: true });
    });
    on('item:use', (data, ack) => {
      const now = Date.now();
      if (!p.active || p.finishTime !== null || !validRevision(data) || !limit(p, 'use', 8) || room.phase !== 'racing' || !p.item || p.itemReady > now || p.state.rescue) return ack({ ok: false });
      const type = p.item, victims = []; p.holding = false;
      if (type === 'star') { p.starUntil = now + 8000; p.shrinkUntil = 0; }
      else if (type === 'lightning') active().forEach(other => { if (other.id !== p.id && other.starUntil <= now && other.finishTime === null) { other.shrinkUntil = now + 6000; damage(other); victims.push(other.id); } });
      else if (!['mushroom', 'triple'].includes(type)) spawnShot(p, type, !!data.forward);
      consume(p);
      io.emit('item:action', { revision: room.revision, owner: p.id, type, count: p.itemCount, item: p.item, victims, at: now });
      ack({ ok: true });
    });
    socket.on('disconnect', () => removePlayer(p, true));
  });
  let previous = Date.now(), broadcastCounter = 0;
  const timer = setInterval(() => {
    const now = Date.now(), dt = Math.min(.05, (now - previous) / 1000); previous = now;
    if (room.phase === 'countdown' && now >= room.startsAt) { room.phase = 'racing'; broadcastRoom(); }
    if (room.phase === 'racing') { updateShots(dt); finishIfReady(now); }
    if (++broadcastCounter % 2 === 0) io.volatile.emit('snapshot', { revision: room.revision, serverTime: now, phase: room.phase,
      players: active().map(p => pose(p, now)), shots: [...shots.values()].map(s => ({ id: s.id, type: s.type, x: s.x, y: s.y, z: s.z, heading: s.heading })) });
  }, 1000 / 60);
function listen(port = process.env.PORT || 3000, host = '0.0.0.0') {
    return new Promise((resolve, reject) => { server.once('error', reject); server.listen(port, host, () => { server.off('error', reject); resolve(server.address()); }); });
  }
  async function close() { if (closed) return; closed = true; clearInterval(timer); await new Promise(resolve => io.close(resolve)); if (server.listening) await new Promise(resolve => server.close(resolve)); }
  return { app, server, io, listen, close, room, players, tracks, shots, resetRace, sample };
}

if (require.main === module) {
  const game = createGameServer(), port = Number(process.env.PORT) || 3000;
  game.listen(port).then(() => {
    console.log('\nRETRO KART LAN · servidor escuchando en 0.0.0.0:' + port);
    console.log('En este ordenador: http://localhost:' + port);
    for (const interfaces of Object.values(os.networkInterfaces())) for (const ip of interfaces || [])
      if (ip.family === 'IPv4' && !ip.internal) console.log('Amigos en la misma Wi-Fi: http://' + ip.address + ':' + port);
    console.log('Ctrl+C para detener el servidor.\n');
  }).catch(error => { console.error(error.code === 'EADDRINUSE' ? 'El puerto ' + port + ' está ocupado. Cierra el otro servidor.' : error); process.exitCode = 1; game.close(); });
  for (const signal of ['SIGINT', 'SIGTERM']) process.once(signal, () => game.close().then(() => process.exit(0)));
}
module.exports = { createGameServer };
