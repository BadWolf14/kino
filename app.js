import { initializeApp } from "https://www.gstatic.com/firebasejs/10.14.1/firebase-app.js";
import { getAuth, signInAnonymously, onAuthStateChanged } from "https://www.gstatic.com/firebasejs/10.14.1/firebase-auth.js";
import {
  getDatabase, ref, set, push, onValue, onChildAdded, onDisconnect,
  serverTimestamp, query, limitToLast
} from "https://www.gstatic.com/firebasejs/10.14.1/firebase-database.js";
import { startHost, startViewer } from "./live.js?v=8";
import { parseExport, parseShareCode, isShareCode, loadLibrary, saveLibrary, clearLibrary, toRoomSource, dataUrlToFile } from "./library.js?v=8";
// config.js is a plain script that declares `firebaseConfig` exactly as Firebase shows it
/* global firebaseConfig */
const FIREBASE_CONFIG = (() => {
  const c = typeof firebaseConfig !== "undefined" ? firebaseConfig : null;
  if (c && !c.databaseURL && c.projectId) c.databaseURL = `https://${c.projectId}-default-rtdb.europe-west1.firebasedatabase.app`;
  return c;
})();

const $ = s => document.querySelector(s);
const CODE_RE = /^[a-z0-9-]{3,32}$/;
const EMOJI = ["😂", "😮", "😍", "😱", "👏", "🔥", "😢", "🍿"];
const store = {
  get(k) { try { return localStorage.getItem(k); } catch { return null; } },
  set(k, v) { try { localStorage.setItem(k, v); } catch {} }
};

// ---------------------------------------------------------------- state
let db, uid = null, serverOffset = 0;
let code = null, joinedAt = 0;
let roomListeners = [];          // refs to detach on leave
let memberRef = null, memberTimer = null;
let S = null;                    // room playback state from Firebase
let lastWrittenV = 0;
let player = null;               // active player adapter
let curSrcKey = null;
let localFile = null, localFileUrl = null, localFileFor = null;
let applyingUntil = 0;
let members = {};
let nick = (store.get("seans.nick") || "").slice(0, 24);
let col = Number(store.get("seans.col"));
if (!(col >= 0 && col < 6)) { col = Math.floor(Math.random() * 6); store.set("seans.col", String(col)); }

const now = () => Date.now();
const serverNow = () => Date.now() + serverOffset;
const myName = () => nick || "Зритель";
const expected = st => st.playing ? st.pos + (serverNow() - st.at) / 1000 : st.pos;
const fmt = s => {
  s = Math.max(0, Math.floor(s || 0));
  const h = Math.floor(s / 3600), m = Math.floor(s % 3600 / 60), x = s % 60;
  return [h, m, x].map(v => String(v).padStart(2, "0")).join(":");
};
// room time, capped at the end of the video so a finished film doesn't keep counting
function roomTime() {
  if (!S) return null;
  const t = expected(S), d = player && player.ready ? player.duration() : 0;
  return d ? Math.min(t, d) : t;
}
const srcKey = src => !src ? null : src.type === "live" ? `live:${src.host}:${src.sid}` : `${src.type}:${src.id || src.url || src.name || ""}`;
const rid = () => Math.random().toString(36).slice(2, 10);
let liveFile = null, liveHost = null, liveViewer = null, liveViewers = 0;
function stopLive() { liveHost?.stop(); liveHost = null; liveViewer?.stop(); liveViewer = null; liveViewers = 0; }

function toast(text) {
  const t = $("#toast"); t.textContent = text; t.hidden = false;
  clearTimeout(toast.timer); toast.timer = setTimeout(() => t.hidden = true, 2400);
}

// ---------------------------------------------------------------- source parsing
function parseSource(raw) {
  raw = raw.trim();
  if (!raw) return null;
  let u;
  if (!/^https?:\/\//i.test(raw) && !/^(www\.)?(youtube\.com|youtu\.be|rutube\.ru)\//i.test(raw)) return { search: raw };
  try { u = new URL(/^https?:/i.test(raw) ? raw : "https://" + raw); } catch { return { error: "Это не похоже на ссылку. Скопируйте адрес целиком, начиная с https://" }; }
  if (u.protocol !== "https:" && u.protocol !== "http:") return { error: "Нужна ссылка, которая начинается с https://" };
  const host = u.hostname.replace(/^www\.|^m\./, "");
  let id = null;
  if (host === "youtu.be") id = u.pathname.slice(1).split("/")[0];
  else if (host === "youtube.com" || host === "music.youtube.com" || host === "youtube-nocookie.com") {
    if (u.pathname === "/watch") id = u.searchParams.get("v");
    else { const m = u.pathname.match(/^\/(shorts|embed|live|v)\/([^/?#]+)/); if (m) id = m[2]; }
  }
  if (host.endsWith("youtube.com") || host === "youtu.be") {
    if (!id || !/^[A-Za-z0-9_-]{6,20}$/.test(id)) return { error: "Не удалось найти видео в этой ссылке YouTube." };
    return { type: "yt", id };
  }
  if (host === "rutube.ru") {
    const m = u.pathname.match(/^\/(?:video|play\/embed|shorts)\/(?:private\/)?([0-9a-f]{32})/i);
    if (!m) return { error: "Не удалось найти видео в этой ссылке RuTube. Нужна ссылка вида rutube.ru/video/…" };
    return { type: "rt", id: m[1].toLowerCase() };
  }
  return { type: "url", url: u.href.slice(0, 1000) };
}

// ---------------------------------------------------------------- player adapters
// Each adapter: ready, time(), duration(), paused(), play() -> Promise, pause(), seek(t), setRate(r), destroy()
// Calls handlers.onPlay / onPause / onSeek(t) for changes the viewer made.

function makeVideoPlayer(srcUrl, handlers, isHls) {
  const host = $("#playerHost");
  const v = document.createElement("video");
  v.controls = true; v.playsInline = true; v.preload = "auto";
  host.replaceChildren(v);
  let hls = null, pendingSeek = false;
  const p = {
    ready: false, kind: "video", el: v,
    time: () => v.currentTime || 0,
    duration: () => v.duration || 0,
    paused: () => v.paused,
    play: () => v.play(),
    pause: () => v.pause(),
    seek: t => { pendingSeek = true; v.currentTime = t; },
    setRate: r => { v.playbackRate = r; },
    destroy: () => { try { hls?.destroy(); } catch {} v.removeAttribute("src"); v.load(); v.remove(); }
  };
  v.addEventListener("loadedmetadata", () => { p.ready = true; handlers.onReady(); });
  v.addEventListener("play", () => handlers.onPlay());
  v.addEventListener("pause", () => { if (!v.ended) handlers.onPause(); });
  v.addEventListener("seeked", () => { if (pendingSeek) { pendingSeek = false; return; } handlers.onSeek(v.currentTime); });
  v.addEventListener("error", () => handlers.onError("Видео не загружается. Проверьте ссылку или формат: браузеры уверенно играют MP4 (H.264) и WebM."));
  if (isHls && window.Hls && window.Hls.isSupported()) {
    hls = new window.Hls();
    hls.loadSource(srcUrl); hls.attachMedia(v);
    hls.on(window.Hls.Events.ERROR, (_, d) => { if (d.fatal) handlers.onError("Поток m3u8 не загружается. Возможно, сервер видео не разрешает воспроизведение с других сайтов."); });
  } else {
    v.src = srcUrl;
  }
  return p;
}

let ytApiPromise = null;
function loadYouTubeApi() {
  if (window.YT && window.YT.Player) return Promise.resolve();
  if (!ytApiPromise) ytApiPromise = new Promise((resolve, reject) => {
    const prev = window.onYouTubeIframeAPIReady;
    window.onYouTubeIframeAPIReady = () => { prev?.(); resolve(); };
    const s = document.createElement("script");
    s.src = "https://www.youtube.com/iframe_api";
    s.onerror = () => reject(new Error("yt"));
    document.head.appendChild(s);
  });
  return ytApiPromise;
}

// Live broadcast viewer: the picture comes from the host's browser, so timing is the host's job
function makeLivePlayer(src) {
  const host = $("#playerHost");
  const v = document.createElement("video");
  v.autoplay = true; v.playsInline = true; v.controls = true;
  host.replaceChildren(v);
  const p = {
    ready: false, kind: "live", el: v, status: "connecting",
    time: () => roomTime() ?? 0,
    duration: () => Number(src.dur) || 0,
    paused: () => v.paused,
    play: () => v.play(),
    pause: () => {}, seek: () => {}, setRate: () => {},
    destroy: () => { liveViewer?.stop(); liveViewer = null; v.srcObject = null; v.remove(); }
  };
  liveViewer = startViewer({
    db, room: code, uid, host: src.host, video: v,
    onStatus: st => {
      p.status = st;
      if (st === "stream" || st === "connected") {
        p.ready = true;
        v.play().then(() => { $("#tapJoin").hidden = true; }).catch(() => { $("#tapJoin").hidden = false; });
      }
      renderSync(); pushMember();
    }
  });
  return p;
}

// RuTube: embedded iframe controlled through its postMessage API (JSON strings {type, data})
function makeRutubePlayer(id, handlers) {
  const host = $("#playerHost");
  const f = document.createElement("iframe");
  f.src = `https://rutube.ru/play/embed/${id}`;
  f.allow = "autoplay; fullscreen; picture-in-picture; clipboard-write";
  f.allowFullscreen = true;
  host.replaceChildren(f);
  let state = "paused", t = 0, tWall = now(), dur = 0, progSeekUntil = 0, destroyed = false;
  const send = (type, data = {}) => { try { f.contentWindow.postMessage(JSON.stringify({ type, data }), "*"); } catch {} };
  const playing = () => state === "playing";
  const cur = () => t + (playing() ? (now() - tWall) / 1000 : 0);
  const p = {
    ready: false, kind: "rt",
    time: cur,
    duration: () => dur,
    paused: () => !playing(),
    play: () => { send("player:play"); return new Promise((res, rej) => setTimeout(() => playing() ? res() : rej(new Error("blocked")), 1800)); },
    pause: () => send("player:pause"),
    seek: s => { progSeekUntil = now() + 2000; t = s; tWall = now(); send("player:setCurrentTime", { time: s }); },
    setRate: () => {},
    destroy: () => { destroyed = true; window.removeEventListener("message", onMsg); f.remove(); }
  };
  function onMsg(e) {
    if (destroyed || e.source !== f.contentWindow) return;
    let m = e.data;
    if (typeof m === "string") { try { m = JSON.parse(m); } catch { return; } }
    if (!m || typeof m.type !== "string") return;
    const d = m.data || {};
    switch (m.type) {
      case "player:ready":
        if (!p.ready) { p.ready = true; handlers.onReady(); }
        break;
      case "player:durationChange":
        if (typeof d.duration === "number") dur = d.duration;
        if (!p.ready) { p.ready = true; handlers.onReady(); }
        break;
      case "player:currentTime":
        if (typeof d.time === "number") {
          const predicted = cur();
          t = d.time; tWall = now();
          if (Math.abs(d.time - predicted) > 2 && now() > progSeekUntil) handlers.onSeek(d.time);
        }
        break;
      case "player:changeState": {
        // seen in practice: playing, pause, paused, stopped, ended, seeking, seeked, buffering
        const st = String(d.state || d.status || "");
        if (st === "playing") { if (state !== "playing") { state = "playing"; tWall = now(); handlers.onPlay(); } }
        else if (/^(pause|paused|stopped|ended)$/.test(st)) { if (state === "playing") { t = cur(); state = "paused"; handlers.onPause(); } }
        break;
      }
      case "player:error":
        handlers.onError("RuTube не может показать это видео. Возможно, оно доступно только на самом RuTube.");
        break;
    }
  }
  window.addEventListener("message", onMsg);
  // some embeds never send player:ready; treat the loaded frame as ready after a moment
  f.addEventListener("load", () => setTimeout(() => { if (!p.ready && !destroyed) { p.ready = true; handlers.onReady(); } }, 2500));
  return p;
}

function makeYouTubePlayer(id, handlers) {
  const host = $("#playerHost");
  const div = document.createElement("div");
  host.replaceChildren(div);
  let yt = null, poll = null, lastT = 0, lastWall = now(), progSeekUntil = 0, destroyed = false;
  const st = () => (yt && yt.getPlayerState ? yt.getPlayerState() : -1);
  const p = {
    ready: false, kind: "yt",
    time: () => (yt && yt.getCurrentTime ? yt.getCurrentTime() : 0),
    duration: () => (yt && yt.getDuration ? yt.getDuration() : 0),
    paused: () => { const s = st(); return !(s === 1 || s === 3); },
    play: () => { yt?.playVideo(); return new Promise((res, rej) => setTimeout(() => (st() === 1 || st() === 3) ? res() : rej(new Error("blocked")), 1500)); },
    pause: () => yt?.pauseVideo(),
    seek: t => { progSeekUntil = now() + 1500; yt?.seekTo(t, true); lastT = t; lastWall = now(); },
    setRate: () => {},
    destroy: () => { destroyed = true; clearInterval(poll); try { yt?.destroy(); } catch {} }
  };
  loadYouTubeApi().then(() => {
    if (destroyed) return;
    yt = new window.YT.Player(div, {
      videoId: id,
      playerVars: { playsinline: 1, rel: 0, modestbranding: 1 },
      events: {
        onReady: () => {
          p.ready = true; handlers.onReady();
          poll = setInterval(() => {
            const t = p.time(), w = now();
            const exp = lastT + (p.paused() ? 0 : (w - lastWall) / 1000);
            if (Math.abs(t - exp) > 1.5 && w > progSeekUntil) handlers.onSeek(t);
            lastT = t; lastWall = w;
          }, 500);
        },
        onStateChange: e => {
          if (e.data === 1) handlers.onPlay();
          else if (e.data === 2) handlers.onPause();
        },
        onError: () => handlers.onError("YouTube не даёт показать это видео на других сайтах. Попробуйте другое видео.")
      }
    });
  }).catch(() => handlers.onError("Не удалось загрузить плеер YouTube. Проверьте интернет или блокировщик рекламы."));
  return p;
}

// ---------------------------------------------------------------- sync logic
const handlers = {
  onReady() { $("#srcErr").hidden = true; applyState(); renderSync(); },
  onPlay() {
    $("#tapJoin").hidden = true; $("#tapHint").hidden = true;
    if (now() < applyingUntil || !S) return;
    if (!S.playing) writeState({ playing: true, pos: player.time() });
  },
  onPause() {
    if (now() < applyingUntil || !S) return;
    if (S.playing) writeState({ playing: false, pos: player.time() });
  },
  onSeek(t) {
    if (now() < applyingUntil || !S) return;
    if (Math.abs(t - expected(S)) > 1.5) writeState({ pos: t, playing: !player.paused() });
  },
  onError(msg) { const e = $("#srcErr"); e.textContent = msg; e.hidden = false; }
};

function writeState(patch) {
  if (!code || !S) return;
  const v = (S.v || 0) + 1;
  S = { ...S, ...patch, v, by: uid, at: serverNow() };
  lastWrittenV = v;
  set(ref(db, `rooms/${code}/state`), S).catch(err => toast("Не удалось сохранить: " + err.message));
  renderSync();
  setTimeout(pushMember, 300);
}

function setSource(src) {
  S = { src, playing: false, pos: 0, at: serverNow(), v: (S?.v || 0) + 1, by: uid };
  lastWrittenV = S.v;
  set(ref(db, `rooms/${code}/state`), S).catch(err => toast("Не удалось сохранить: " + err.message));
  loadSource(src);
}

function loadSource(src) {
  const key = srcKey(src);
  if (key === curSrcKey && player) return;
  stopLive();
  player?.destroy(); player = null; curSrcKey = key;
  $("#srcErr").hidden = true; $("#tapJoin").hidden = true; $("#tapHint").hidden = true;
  const drop = $("#drop");
  $("#dropLive").hidden = true;
  if (!src) { drop.hidden = false; $("#dropPick").hidden = true; $("#dropTitle").textContent = "Что смотрим?"; $("#dropText").textContent = "Вставьте ссылку сверху или выберите файл. Видео сразу появится у всех в комнате."; renderSync(); return; }
  if (src.type === "yt") { drop.hidden = true; player = makeYouTubePlayer(src.id, handlers); }
  else if (src.type === "rt") { drop.hidden = true; player = makeRutubePlayer(src.id, handlers); }
  else if (src.type === "url") { drop.hidden = true; player = makeVideoPlayer(src.url, handlers, /\.m3u8($|\?)/i.test(src.url)); }
  else if (src.type === "live") {
    if (src.host !== uid) { drop.hidden = true; player = makeLivePlayer(src); }
    else if (liveFile && liveFile.liveSid === src.sid) {
      drop.hidden = true;
      if (localFileUrl) URL.revokeObjectURL(localFileUrl);
      localFileUrl = URL.createObjectURL(liveFile);
      player = makeVideoPlayer(localFileUrl, handlers, false);
      try {
        liveHost = startHost({ db, room: code, uid, video: player.el, onViewers: n => { liveViewers = n; renderSync(); } });
      } catch (e) { const er = $("#srcErr"); er.textContent = e.message; er.hidden = false; }
    } else {
      drop.hidden = false; $("#dropPick").hidden = true; $("#dropLive").hidden = false;
      $("#dropTitle").textContent = "Трансляция остановилась";
      $("#dropText").textContent = `Вы транслировали «${src.title || "файл"}», но страница перезагрузилась. Выберите этот файл снова, чтобы продолжить для всех.`;
    }
  }
  else if (src.type === "file") {
    if (localFile && (localFile.name === src.name || localFileFor === src.name)) {
      drop.hidden = true;
      if (localFileUrl) URL.revokeObjectURL(localFileUrl);
      localFileUrl = URL.createObjectURL(localFile);
      player = makeVideoPlayer(localFileUrl, handlers, false);
    } else {
      drop.hidden = false; $("#dropPick").hidden = false;
      $("#dropTitle").textContent = "Откройте свою копию этого файла";
      $("#dropText").textContent = `Комната смотрит файл «${src.name}». Видео не пересылается: выберите такой же файл на своём устройстве, и плеер перемотает на нужную секунду.`;
    }
  }
  renderSync();
}

function applyState() {
  if (!player || !player.ready || !S) return;
  if (player.kind === "live") {
    if (player.paused()) Promise.resolve(player.play()).catch(() => { $("#tapJoin").hidden = false; });
    setTimeout(pushMember, 1500);
    return;
  }
  applyingUntil = now() + 1200;
  const dur = player.duration();
  let want = Math.max(0, expected(S));
  if (dur) want = Math.min(want, dur - 0.1);
  if (Math.abs(player.time() - want) > 1) player.seek(want);
  if (S.playing && player.paused()) {
    Promise.resolve(player.play()).catch(() => {
      // a cross-origin player (YouTube, RuTube) only starts from a click inside it
      if (player && player.kind !== "video") $("#tapHint").hidden = false; else $("#tapJoin").hidden = false;
    });
  } else if (!S.playing && !player.paused()) {
    player.pause();
  }
  if (!S.playing) player.setRate(1);
  setTimeout(pushMember, 1500);
}

$("#tapBtn").onclick = () => {
  $("#tapJoin").hidden = true;
  if (!player) return;
  applyingUntil = now() + 1200;
  Promise.resolve(player.play()).catch(() => {});
  setTimeout(applyState, 300);
};

// drift correction
setInterval(() => {
  if (player && player.ready && player.kind !== "live" && S && S.playing && !player.paused()) {
    const diff = player.time() - expected(S);
    const hard = player.kind === "video" ? 1.0 : 1.5;
    if (Math.abs(diff) > hard) { player.setRate(1); applyState(); }
    else if (player.kind === "video" && Math.abs(diff) > 0.25) player.setRate(diff > 0 ? 0.95 : 1.05);
    else player.setRate(1);
  }
  renderSync();
  if (code) renderPeople();
}, 1000);

// ---------------------------------------------------------------- rendering
function renderSync() {
  const chip = $("#syncChip"); chip.className = "chip";
  $("#tc").textContent = S ? `${fmt(roomTime())}${player?.duration() ? " / " + fmt(player.duration()) : ""}` : "00:00:00";
  const src = S?.src;
  $("#srcLabel").textContent = !src ? "Ничего не выбрано"
    : src.title ? String(src.title).slice(0, 160)
    : src.type === "yt" ? "YouTube · " + src.id
    : src.type === "rt" ? "RuTube · " + src.id
    : src.type === "url" ? src.url
    : src.type === "live" ? "Трансляция"
    : "Файл · " + src.name;
  if (!src) chip.textContent = "Ничего не выбрано";
  else if (src.type === "live" && src.host === uid && player) {
    chip.textContent = liveViewers ? `Вы транслируете · ${liveViewers} зр.` : "Вы транслируете · ждём зрителей";
    chip.classList.add("ok");
  }
  else if (src.type === "live" && player?.kind === "live") {
    const st = player.status;
    if (st === "connected" || st === "stream") { chip.textContent = S.playing ? "Трансляция идёт" : "Пауза у всех"; chip.classList.add("ok"); }
    else if (st === "connecting") chip.textContent = "Подключение к трансляции…";
    else { chip.textContent = st === "nohost" ? "Транслирующий не отвечает…" : "Нет связи, переподключаюсь…"; chip.classList.add("warn"); }
  }
  else if (!player || !player.ready) chip.textContent = src.type === "file" && !player ? "Нужен файл" : "Загрузка…";
  else if (!S.playing) chip.textContent = "Пауза у всех";
  else {
    const diff = Math.abs(player.time() - roomTime());
    if (diff < 1.2) { chip.textContent = "В синхроне"; chip.classList.add("ok"); }
    else { chip.textContent = "Догоняем…"; chip.classList.add("warn"); }
  }
  const mm = $("#mismatch");
  if (src?.type === "file" && player?.ready && src.dur && Math.abs(src.dur - player.duration()) > 3) {
    mm.hidden = false;
    mm.textContent = `Похоже, у вас другой файл: длительность ${fmt(player.duration())}, а у того, кто его поставил, ${fmt(src.dur)}. Проверьте, что серия та же.`;
  } else mm.hidden = true;
}

function avatar(name, c) {
  const a = document.createElement("span"); a.className = "av";
  a.style.background = `var(--c${c})`; a.textContent = (name.trim()[0] || "?").toUpperCase(); return a;
}

function renderPeople() {
  const ul = $("#people"); ul.replaceChildren();
  const list = Object.entries(members);
  $("#peopleLabel").textContent = `В зале · ${list.length || 1}`;
  const roomT = roomTime();
  for (const [id, m] of list) {
    const name = String(m.nick || "Зритель").slice(0, 24);
    const li = document.createElement("li");
    li.appendChild(avatar(name, (Number(m.col) | 0) % 6));
    const nm = document.createElement("span"); nm.className = "nm"; nm.textContent = name + (id === uid ? " (вы)" : ""); li.appendChild(nm);
    // where this viewer is right now: own row from the live player, others extrapolated from their last report
    let t = null, playing = false, ready = !!m.ready;
    if (id === uid && player && player.ready) { t = player.time(); playing = !player.paused(); ready = true; }
    else if (ready && typeof m.pos === "number" && typeof m.at === "number") {
      playing = !!m.playing;
      t = m.pos + (playing ? Math.max(0, serverNow() - m.at) / 1000 : 0);
    }
    const tc = document.createElement("span"); tc.className = "pt mono";
    tc.textContent = t == null ? "--:--:--" : fmt(t);
    const st = document.createElement("span"); st.className = "st";
    if (S?.src?.type === "live") {
      if (id === S.src.host) { st.textContent = "транслирует"; st.classList.add("ok"); }
      else {
        const ls = id === uid ? player?.status : m.ls;
        if (ls === "connected" || ls === "stream") { st.textContent = "смотрит трансляцию"; st.classList.add("ok"); }
        else if (ls === "connecting" || !ls) st.textContent = "подключается";
        else { st.textContent = "нет связи"; st.classList.add("warn"); }
      }
    }
    else if (!ready) st.textContent = S?.src?.type === "file" ? "ждёт файл" : "загружается";
    else if (t != null && roomT != null) {
      const lag = t - roomT;
      const a = Math.abs(lag);
      if (a < 1.5) { st.textContent = a < 0.1 ? "точно" : `${lag > 0 ? "+" : "−"}${a.toFixed(1)} с`; st.classList.add("ok"); }
      else { st.textContent = `${lag > 0 ? "впереди на" : "отстаёт на"} ${a < 10 ? a.toFixed(1) : Math.round(a)} с`; st.classList.add("warn"); }
      if (!playing && S.playing) st.textContent += " · пауза";
    } else st.textContent = "готов";
    const right = document.createElement("span"); right.className = "pr"; right.append(tc, st);
    li.appendChild(right); ul.appendChild(li);
  }
}

function addChatMessage(m) {
  const box = $("#chat");
  box.querySelector(".empty")?.remove();
  const atBottom = box.scrollHeight - box.scrollTop - box.clientHeight < 40;
  const d = document.createElement("div"); d.className = "msg";
  const w = document.createElement("span"); w.className = "who"; w.style.color = `var(--c${(Number(m.col) | 0) % 6})`; w.textContent = String(m.nick || "Зритель").slice(0, 24);
  const x = document.createElement("span"); x.textContent = String(m.text || "").slice(0, 500);
  const t = document.createElement("span"); t.className = "t mono";
  t.textContent = typeof m.ts === "number" ? new Date(m.ts - serverOffset).toLocaleTimeString("ru-RU", { hour: "2-digit", minute: "2-digit" }) : "";
  d.append(w, x, t); box.appendChild(d);
  while (box.children.length > 200) box.firstChild.remove();
  if (atBottom || m.uid === uid) box.scrollTop = box.scrollHeight;
}

function flyEmoji(e, who) {
  const el = document.createElement("div"); el.className = "fly";
  el.style.left = (8 + Math.random() * 80) + "%";
  el.textContent = e;
  const s = document.createElement("small"); s.textContent = who; el.appendChild(s);
  $("#floats").appendChild(el); setTimeout(() => el.remove(), 2700);
}

// ---------------------------------------------------------------- room lifecycle
function listen(r, type, cb) {
  const unsub = type === "value" ? onValue(r, cb) : onChildAdded(r, cb);
  roomListeners.push(unsub);
}

function pushMember() {
  if (!memberRef) return;
  set(memberRef, {
    nick: myName(), col,
    ready: !!(player && player.ready),
    playing: !!(player && player.ready && !player.paused()),
    pos: player && player.ready ? player.time() : 0,
    ls: player?.kind === "live" ? player.status : null,
    at: serverNow()
  }).catch(() => {});
}

function joinRoom(c) {
  c = String(c || "").trim().toLowerCase();
  if (!CODE_RE.test(c)) { $("#codeErr").hidden = false; return; }
  $("#codeErr").hidden = true;
  if (code) leaveRoom(true);
  code = c; joinedAt = serverNow(); S = null; curSrcKey = null; members = {};
  $("#roomCode").textContent = c;
  $("#chat").replaceChildren(Object.assign(document.createElement("span"), { className: "empty", textContent: "Пока тихо. Напишите первым." }));
  $("#lobby").hidden = true; $("#roomView").hidden = false;
  if (location.hash !== "#" + c) history.replaceState(null, "", "#" + c);

  memberRef = ref(db, `rooms/${c}/members/${uid}`);
  onDisconnect(memberRef).remove();
  pushMember();
  memberTimer = setInterval(pushMember, 2000);

  listen(ref(db, `rooms/${c}/state`), "value", snap => {
    const val = snap.val();
    if (!val || typeof val !== "object") { S = null; loadSource(null); return; }
    const own = val.by === uid && val.v === lastWrittenV;
    S = {
      src: val.src && typeof val.src === "object" ? val.src : null,
      playing: !!val.playing, pos: Number(val.pos) || 0, at: Number(val.at) || serverNow(),
      v: Number(val.v) || 0, by: String(val.by || "")
    };
    loadSource(S.src);
    if (!own) applyState();
    renderSync(); renderPeople();
  });
  listen(ref(db, `rooms/${c}/members`), "value", snap => { members = snap.val() || {}; renderPeople(); });
  listen(query(ref(db, `rooms/${c}/chat`), limitToLast(100)), "child", snap => addChatMessage(snap.val() || {}));
  listen(query(ref(db, `rooms/${c}/reactions`), limitToLast(1)), "child", snap => {
    const r = snap.val() || {};
    if (typeof r.ts === "number" && r.ts < joinedAt - 3000) return;
    if (EMOJI.includes(r.e)) flyEmoji(r.e, String(r.nick || "Зритель").slice(0, 24));
  });
}

function leaveRoom(silent) {
  roomListeners.forEach(u => u()); roomListeners = [];
  clearInterval(memberTimer);
  if (memberRef) { set(memberRef, null).catch(() => {}); onDisconnect(memberRef).cancel(); memberRef = null; }
  stopLive();
  player?.destroy(); player = null; curSrcKey = null; S = null; code = null;
  if (!silent) {
    $("#roomView").hidden = true; $("#lobby").hidden = false;
    history.replaceState(null, "", location.pathname + location.search);
  }
}

// ---------------------------------------------------------------- search
let searchTab = "rutube", searchSeq = 0;
/* global youtubeApiKey */
const ytKey = () => (typeof youtubeApiKey === "string" ? youtubeApiKey.trim() : "");

function closeResults() { $("#results").hidden = true; $("#resultsGrid").replaceChildren(); }
function resultsMessage(text, label) {
  $("#results").hidden = false;
  $("#resultsLabel").textContent = label || "Результаты";
  const e = document.createElement("p"); e.className = "empty"; e.textContent = text;
  $("#resultsGrid").replaceChildren(e);
}
function showYouTubeHelp() {
  resultsMessage("Для поиска по YouTube нужен бесплатный ключ YouTube API. Его вставляют в файл youtube-key.js, инструкция в README. Ссылку на видео YouTube можно вставить и без ключа.", "YouTube");
}
const fmtDur = s => { s = Math.round(Number(s) || 0); if (!s) return ""; const h = Math.floor(s / 3600), m = Math.floor(s % 3600 / 60), x = s % 60; return (h ? h + ":" + String(m).padStart(2, "0") : m) + ":" + String(x).padStart(2, "0"); };
const isoDur = iso => { const m = /PT(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?/.exec(iso || ""); return m ? (+m[1] || 0) * 3600 + (+m[2] || 0) * 60 + (+m[3] || 0) : 0; };
const safeImg = u => (typeof u === "string" && /^https:\/\//.test(u)) ? u : "";

// RuTube's search API refuses requests from other sites (CORS), so without a proxy the tab
// opens the search on rutube.ru and the viewer pastes the video link back here.
/* global rutubeProxy */
const RUTUBE_PROXY = (typeof rutubeProxy === "string" && /^https:\/\//.test(rutubeProxy)) ? rutubeProxy.replace(/\/$/, "") : "";
function showRutubeLink(q) {
  resultsMessage("RuTube не разрешает искать по своему каталогу с других сайтов. Откройте поиск на RuTube, выберите видео, скопируйте ссылку на него и вставьте её сюда: оно сразу появится у всех.", `RuTube · «${q}»`);
  const a = document.createElement("a");
  a.className = "btn primary"; a.target = "_blank"; a.rel = "noopener";
  a.href = `https://rutube.ru/search/?query=${encodeURIComponent(q)}`;
  a.textContent = `Искать «${q}» на RuTube`;
  const wrap = document.createElement("div"); wrap.className = "empty"; wrap.appendChild(a);
  $("#resultsGrid").appendChild(wrap);
}
async function searchRutube(q) {
  const r = await fetch(`${RUTUBE_PROXY}/api/search/video/?query=${encodeURIComponent(q)}&page=1`);
  if (!r.ok) throw new Error("rutube " + r.status);
  const j = await r.json();
  return (j.results || []).map(v => {
    const id = String(v.id || (String(v.video_url || "").match(/[0-9a-f]{32}/) || [""])[0]).toLowerCase();
    return /^[0-9a-f]{32}$/.test(id) ? {
      src: { type: "rt", id, title: String(v.title || "").slice(0, 160) },
      title: v.title || "Без названия", meta: v.author?.name || "", thumb: safeImg(v.thumbnail_url), dur: fmtDur(v.duration)
    } : null;
  }).filter(Boolean);
}

async function searchYouTube(q) {
  const key = ytKey();
  const r = await fetch(`https://www.googleapis.com/youtube/v3/search?part=snippet&type=video&videoEmbeddable=true&maxResults=24&q=${encodeURIComponent(q)}&key=${encodeURIComponent(key)}`);
  const j = await r.json();
  if (j.error) throw new Error(j.error.message || "youtube");
  const items = (j.items || []).filter(i => i.id?.videoId);
  // durations come from a second call; skip quietly if it fails
  let durs = {};
  try {
    const ids = items.map(i => i.id.videoId).join(",");
    const d = await (await fetch(`https://www.googleapis.com/youtube/v3/videos?part=contentDetails&id=${ids}&key=${encodeURIComponent(key)}`)).json();
    for (const v of d.items || []) durs[v.id] = isoDur(v.contentDetails?.duration);
  } catch {}
  const decode = s => { const t = document.createElement("textarea"); t.innerHTML = s; return t.value; };
  return items.map(i => ({
    src: { type: "yt", id: i.id.videoId, title: decode(i.snippet.title || "").slice(0, 160) },
    title: decode(i.snippet.title || ""), meta: decode(i.snippet.channelTitle || ""),
    thumb: safeImg(i.snippet.thumbnails?.medium?.url), dur: fmtDur(durs[i.id.videoId])
  }));
}

async function searchArchive(q) {
  const query = `(${q}) AND mediatype:(movies) AND NOT collection:(tvnews)`;
  const url = `https://archive.org/advancedsearch.php?q=${encodeURIComponent(query)}&fl[]=identifier&fl[]=title&fl[]=year&fl[]=creator&sort[]=downloads+desc&rows=24&output=json`;
  const j = await (await fetch(url)).json();
  return (j.response?.docs || []).filter(d => /^[A-Za-z0-9._-]+$/.test(d.identifier || "")).map(d => ({
    archive: d.identifier,
    title: Array.isArray(d.title) ? d.title[0] : (d.title || d.identifier),
    meta: [d.year, Array.isArray(d.creator) ? d.creator[0] : d.creator].filter(Boolean).join(" · "),
    thumb: `https://archive.org/services/img/${d.identifier}`, dur: ""
  }));
}

// pick a browser-playable video file from an Archive.org item
async function resolveArchive(id, title) {
  const j = await (await fetch(`https://archive.org/metadata/${encodeURIComponent(id)}`)).json();
  const files = (j.files || []).filter(f => typeof f.name === "string");
  const pick = files.find(f => /\.mp4$/i.test(f.name) && /h\.264|mpeg4/i.test(f.format || ""))
    || files.find(f => /\.mp4$/i.test(f.name))
    || files.find(f => /\.(webm|ogv)$/i.test(f.name));
  if (!pick) throw new Error("В этой записи нет видео, которое играет в браузере.");
  const path = pick.name.split("/").map(encodeURIComponent).join("/");
  return { type: "url", url: `https://archive.org/download/${encodeURIComponent(id)}/${path}`, title: String(title || id).slice(0, 160) };
}

async function runSearch(q) {
  const seq = ++searchSeq;
  const names = { rutube: "RuTube", youtube: "YouTube", archive: "Archive.org" };
  if (searchTab === "library") { showLibrary(q); return; }
  if (searchTab === "youtube" && !ytKey()) { showYouTubeHelp(); return; }
  if (searchTab === "rutube" && !RUTUBE_PROXY) { showRutubeLink(q); return; }
  resultsMessage("Ищу…", `${names[searchTab]} · «${q}»`);
  let list;
  try {
    list = searchTab === "rutube" ? await searchRutube(q) : searchTab === "youtube" ? await searchYouTube(q) : await searchArchive(q);
  } catch (err) {
    if (seq !== searchSeq) return;
    resultsMessage(searchTab === "rutube"
      ? "RuTube не ответил на поиск. Попробуйте ещё раз или вставьте ссылку на видео RuTube."
      : searchTab === "youtube" ? "YouTube не принял запрос: " + err.message
      : "Archive.org не ответил. Попробуйте ещё раз чуть позже.", names[searchTab]);
    return;
  }
  if (seq !== searchSeq) return;
  if (!list.length) { resultsMessage("Ничего не нашлось. Попробуйте другое название или другой источник.", `${names[searchTab]} · «${q}»`); return; }
  $("#resultsLabel").textContent = `${names[searchTab]} · «${q}» · ${list.length}`;
  const grid = $("#resultsGrid"); grid.replaceChildren();
  for (const it of list) {
    const b = document.createElement("button"); b.type = "button"; b.className = "card";
    const th = document.createElement("div"); th.className = "thumb";
    if (it.thumb) { const im = document.createElement("img"); im.loading = "lazy"; im.alt = ""; im.referrerPolicy = "no-referrer"; im.src = it.thumb; th.appendChild(im); }
    if (it.dur) { const d = document.createElement("span"); d.className = "dur"; d.textContent = it.dur; th.appendChild(d); }
    const t = document.createElement("span"); t.className = "ttl"; t.textContent = it.title;
    const m = document.createElement("span"); m.className = "meta"; m.textContent = it.meta;
    b.append(th, t, m);
    b.onclick = async () => {
      if (it.archive) {
        b.disabled = true;
        try { const src = await resolveArchive(it.archive, it.title); closeResults(); setSource(src); }
        catch (e) { b.disabled = false; const er = $("#srcErr"); er.textContent = e.message || "Не удалось открыть запись Archive.org."; er.hidden = false; }
        return;
      }
      closeResults(); $("#srcInput").value = ""; setSource(it.src);
    };
    grid.appendChild(b);
  }
}

// ---------------------------------------------------------------- «Моя коллекция» (Framesearch)
let pendingImport = null;
const el = (tag, cls, text) => { const e = document.createElement(tag); if (cls) e.className = cls; if (text != null) e.textContent = text; return e; };
const safePoster = u => (typeof u === "string" && (/^https:\/\//.test(u) || /^data:image\/(png|jpe?g|webp|gif|avif);/i.test(u))) ? u : "";
const typeName = t => ({ movie: "фильм", series: "сериал", anime: "аниме" }[t] || "");

function libHead(label, actions) {
  $("#results").hidden = false;
  $("#resultsLabel").textContent = label;
  const grid = $("#resultsGrid"); grid.replaceChildren();
  const bar = $("#libBar") || el("div", "libbar");
  bar.id = "libBar"; bar.replaceChildren(...actions);
  grid.appendChild(bar);
  return grid;
}
const libBtn = (text, fn, primary) => { const b = el("button", "btn small" + (primary ? " primary" : " ghost"), text); b.type = "button"; b.onclick = fn; return b; };
const libUpload = text => { const l = el("label", "btn small primary", text); l.htmlFor = "libFile"; return l; };

async function importPending(password) {
  if (!pendingImport) return;
  const { kind, text } = pendingImport;
  try {
    const data = kind === "code" ? await parseShareCode(text, password) : await parseExport(text, password);
    pendingImport = null;
    if (kind === "code") { $("#srcInput").value = ""; showEntries(data, "Код из Framesearch", false); return; }
    await saveLibrary(data);
    toast(`Коллекция загружена: ${data.videos.length} видео`);
    selectTab("library"); showLibrary("");
  } catch (e) {
    if (e.needPassword || /пароль/i.test(e.message)) { askPassword(e.message); return; }
    pendingImport = null;
    resultsMessage(e.message || "Не удалось прочитать файл.", "Моя коллекция");
  }
}

function askPassword(msg) {
  const grid = libHead("Моя коллекция", []);
  const f = el("form", "pwform");
  const p = el("p", "empty", msg);
  const i = el("input"); i.type = "password"; i.id = "libPass"; i.placeholder = "Пароль экспорта"; i.autocomplete = "off";
  const b = el("button", "btn primary", "Открыть"); b.type = "submit";
  f.append(p, i, b);
  f.onsubmit = e => { e.preventDefault(); importPending(i.value); };
  grid.appendChild(f); i.focus();
}

function selectTab(name) {
  searchTab = name;
  document.querySelectorAll(".tab").forEach(x => x.setAttribute("aria-selected", String(x.dataset.src === name)));
}

async function showLibrary(filter) {
  const lib = await loadLibrary();
  if (!lib || !lib.videos?.length) {
    const grid = libHead("Моя коллекция", [libUpload("Загрузить экспорт Framesearch")]);
    const p = el("div", "empty libhelp");
    p.append(
      el("p", null, "Сюда можно подключить вашу коллекцию из Framesearch. В Framesearch откройте «Импорт/Экспорт» → «Экспорт» и загрузите сохранённый файл кнопкой выше."),
      el("p", null, "Код «Поделиться» (начинается с P: или E:) можно просто вставить в строку поиска."),
      el("p", "muted", "Коллекция остаётся только в этом браузере. В комнату уходит лишь то видео, которое вы выберете.")
    );
    grid.appendChild(p);
    return;
  }
  const q = String(filter || "").trim().toLowerCase();
  const list = q ? { videos: lib.videos.filter(v => [v.title, v.year, v.genre].join(" ").toLowerCase().includes(q)), episodes: lib.episodes } : lib;
  showEntries(list, `Моя коллекция · ${list.videos.length}${q ? ` из ${lib.videos.length}` : ""}`, true);
}

function showEntries(data, label, isLibrary) {
  const actions = isLibrary ? [libUpload("Обновить"), libBtn("Убрать коллекцию", async () => { await clearLibrary(); showLibrary(""); })] : [];
  const grid = libHead(label, actions);
  if (!data.videos.length) { grid.appendChild(el("p", "empty", "Ничего не нашлось.")); return; }
  for (const v of data.videos) {
    const eps = data.episodes.filter(e => e.videoId === v.id && (e.sourceUrl || "")).sort((a, b) => a.season - b.season || a.episode - b.episode);
    const meta = [v.year, typeName(v.type), eps.length ? `${eps.length} сер.` : ""].filter(Boolean).join(" · ");
    const check = eps.length ? null : toRoomSource(v, v.title, parseSource);
    grid.appendChild(entryCard(v.title, meta, safePoster(v.poster), check && check.error, () => {
      if (eps.length) showEpisodes(v, eps, () => showEntries(data, label, isLibrary));
      else pickEntry(check, v.title);
    }));
  }
}

function showEpisodes(v, eps, back) {
  const grid = libHead(v.title, [libBtn("← Назад", back)]);
  for (const e of eps) {
    const name = `S${e.season}E${e.episode}${e.title ? " · " + e.title : ""}`;
    const check = toRoomSource({ ...e, sourceCategory: v.sourceCategory }, `${v.title} · ${name}`, parseSource);
    grid.appendChild(entryCard(name, v.title, safePoster(v.poster), check.error, () => pickEntry(check, `${v.title} · ${name}`)));
  }
}

function entryCard(title, meta, poster, problem, onClick) {
  const b = el("button", "card" + (problem ? " off" : "")); b.type = "button";
  const th = el("div", "thumb poster");
  if (poster) { const im = el("img"); im.loading = "lazy"; im.alt = ""; im.referrerPolicy = "no-referrer"; im.src = poster; th.appendChild(im); }
  if (problem) th.appendChild(el("span", "dur", "не синхронизируется"));
  b.append(th, el("span", "ttl", title), el("span", "meta", meta));
  if (problem) b.title = problem;
  b.onclick = onClick;
  return b;
}

function pickEntry(check, title) {
  if (check.error) { const er = $("#srcErr"); er.textContent = check.error; er.hidden = false; return; }
  $("#srcErr").hidden = true;
  if (check.file) {
    try { useLocalFile(dataUrlToFile(check.file, title)); closeResults(); }
    catch { const er = $("#srcErr"); er.textContent = "Не удалось открыть видео из коллекции."; er.hidden = false; }
    return;
  }
  closeResults(); setSource(check.src);
}

// ---------------------------------------------------------------- UI wiring
function wireUi() {
  const nickInput = $("#nickInput");
  nickInput.value = nick;
  nickInput.addEventListener("change", () => {
    nick = nickInput.value.trim().slice(0, 24); store.set("seans.nick", nick); pushMember();
  });

  EMOJI.forEach(e => {
    const b = document.createElement("button"); b.type = "button"; b.textContent = e; b.title = "Реакция";
    b.onclick = () => {
      if (!code) return;
      push(ref(db, `rooms/${code}/reactions`), { e, nick: myName(), uid, ts: serverTimestamp() }).catch(() => {});
    };
    $("#reacts").appendChild(b);
  });

  $("#createBtn").onclick = () => joinRoom("kino-" + Math.floor(1000 + Math.random() * 9000));
  $("#joinForm").addEventListener("submit", e => { e.preventDefault(); joinRoom($("#codeInput").value); });
  $("#leaveBtn").onclick = () => leaveRoom(false);
  $("#copyBtn").onclick = async () => {
    try { await navigator.clipboard.writeText(location.href); toast("Ссылка скопирована — отправьте её друзьям"); }
    catch { toast(location.href); }
  };
  $("#cinemaBtn").onclick = () => { $("#screen").requestFullscreen?.().catch(() => {}); };

  $("#srcForm").addEventListener("submit", e => {
    e.preventDefault();
    const raw = $("#srcInput").value.trim();
    if (isShareCode(raw)) { pendingImport = { kind: "code", text: raw }; importPending(""); return; }
    const res = parseSource(raw);
    if (!res) return;
    $("#srcErr").hidden = true;
    if (res.search) { runSearch(res.search); return; }
    if (res.error) { const er = $("#srcErr"); er.textContent = res.error; er.hidden = false; return; }
    $("#srcInput").value = ""; closeResults();
    setSource(res);
  });

  document.querySelectorAll(".tab").forEach(b => b.addEventListener("click", () => {
    searchTab = b.dataset.src;
    document.querySelectorAll(".tab").forEach(x => x.setAttribute("aria-selected", String(x === b)));
    const q = $("#srcInput").value.trim();
    const parsed = q ? parseSource(q) : null;
    if (searchTab === "library") showLibrary(parsed && parsed.search ? parsed.search : "");
    else if (parsed && parsed.search) runSearch(parsed.search);
    else if (searchTab === "youtube" && !ytKey()) showYouTubeHelp();
    else $("#srcInput").focus();
  }));
  $("#srcInput").addEventListener("input", () => {
    const v = $("#srcInput").value;
    $("#srcSubmit").textContent = isShareCode(v) ? "Открыть" : parseSource(v)?.search ? "Найти" : "Поставить";
  });
  $("#resultsClose").onclick = closeResults;

  $("#fileInput").addEventListener("change", () => {
    const f = $("#fileInput").files[0]; $("#fileInput").value = "";
    useLocalFile(f);
  });
  $("#libFile").addEventListener("change", async () => {
    const f = $("#libFile").files[0]; $("#libFile").value = "";
    if (!f) return;
    pendingImport = { kind: "file", text: await f.text() };
    importPending("");
  });
}

function useLocalFile(f) {
    if (!f || !code) return;
    localFile = f; localFileFor = null;
    // the room already plays a file and this viewer has no player yet: this is their own copy of it
    if (S?.src?.type === "file" && (!player || S.src.name === f.name)) { localFileFor = S.src.name; curSrcKey = null; loadSource(S.src); return; }
    // new file for the whole room: read its duration first so others can check they have the same one
    const probe = document.createElement("video"); probe.preload = "metadata";
    const url = URL.createObjectURL(f);
    probe.onloadedmetadata = () => { const dur = probe.duration || 0; URL.revokeObjectURL(url); setSource({ type: "file", name: f.name.slice(0, 200), size: f.size, dur }); };
    probe.onerror = () => { URL.revokeObjectURL(url); setSource({ type: "file", name: f.name.slice(0, 200), size: f.size, dur: 0 }); };
    probe.src = url;
}

function wireUi2() {
  $("#liveInput").addEventListener("change", () => {
    const f = $("#liveInput").files[0]; $("#liveInput").value = "";
    if (!f || !code) return;
    const er = $("#srcErr");
    if (!(HTMLMediaElement.prototype.captureStream || HTMLMediaElement.prototype.mozCaptureStream) || typeof RTCPeerConnection === "undefined") {
      er.textContent = "Транслировать можно из Chrome или Edge на компьютере. Смотреть трансляцию — с любого устройства."; er.hidden = false; return;
    }
    er.hidden = true;
    const sid = rid();
    f.liveSid = sid; liveFile = f;
    const probe = document.createElement("video"); probe.preload = "metadata";
    const url = URL.createObjectURL(f);
    const go = dur => { URL.revokeObjectURL(url); setSource({ type: "live", host: uid, sid, title: f.name.slice(0, 160), dur }); };
    probe.onloadedmetadata = () => go(probe.duration || 0);
    probe.onerror = () => go(0);
    probe.src = url;
  });
  const screen = $("#screen");
  ["dragenter", "dragover"].forEach(ev => screen.addEventListener(ev, e => { e.preventDefault(); $("#drop").classList.add("over"); }));
  ["dragleave", "drop"].forEach(ev => screen.addEventListener(ev, e => { e.preventDefault(); $("#drop").classList.remove("over"); }));
  screen.addEventListener("drop", e => {
    const f = e.dataTransfer?.files?.[0]; if (!f) return;
    const dt = new DataTransfer(); dt.items.add(f); $("#fileInput").files = dt.files;
    $("#fileInput").dispatchEvent(new Event("change"));
  });

  $("#chatForm").addEventListener("submit", e => {
    e.preventDefault();
    const text = $("#chatInput").value.trim().slice(0, 500);
    if (!text || !code) return;
    $("#chatInput").value = "";
    push(ref(db, `rooms/${code}/chat`), { uid, nick: myName(), col, text, ts: serverTimestamp() })
      .catch(err => toast("Сообщение не отправлено: " + err.message));
  });

  window.addEventListener("hashchange", () => {
    const h = location.hash.slice(1).toLowerCase();
    if (CODE_RE.test(h) && h !== code) joinRoom(h);
  });
}

function setConn(on) {
  $("#connDot").className = "dot " + (on ? "on" : "off");
  $("#connText").textContent = on ? "Онлайн" : "Нет связи";
}

// ---------------------------------------------------------------- boot
function showSetup(msg) {
  $("#setup").hidden = false; $("#lobby").hidden = true; $("#roomView").hidden = true;
  $("#setupErr").textContent = msg || "";
  $("#connText").textContent = "Не настроено";
}

(function boot() {
  if (!FIREBASE_CONFIG || /ВСТАВЬТЕ|ВАШ-ПРОЕКТ/.test(JSON.stringify(FIREBASE_CONFIG))) { showSetup(); return; }
  let app;
  try {
    app = initializeApp(FIREBASE_CONFIG);
    db = getDatabase(app);
  } catch (e) { showSetup("Ошибка в config.js: " + e.message); return; }

  onValue(ref(db, ".info/serverTimeOffset"), s => { serverOffset = Number(s.val()) || 0; });
  onValue(ref(db, ".info/connected"), s => setConn(!!s.val()));

  const auth = getAuth(app);
  wireUi();
  wireUi2();
  onAuthStateChanged(auth, user => {
    if (!user) return;
    const first = !uid;
    uid = user.uid;
    if (!first) return;
    $("#lobby").hidden = false;
    const h = location.hash.slice(1).toLowerCase();
    if (CODE_RE.test(h)) joinRoom(h);
  });
  signInAnonymously(auth).catch(e => {
    showSetup(e.code === "auth/operation-not-allowed" || e.code === "auth/admin-restricted-operation"
      ? "Включите анонимный вход: Firebase Console → Authentication → Sign-in method → Anonymous → Enable."
      : "Не удалось войти в Firebase: " + e.message);
  });
})();
