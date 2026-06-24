const { app, BrowserWindow, ipcMain, dialog, safeStorage, Notification, powerSaveBlocker, globalShortcut, Tray, Menu, nativeImage, shell } = require('electron');
const path = require('path');
const fs = require('fs');
const { PassThrough, Transform } = require('stream');
const { spawn } = require('child_process');
const { Client, GatewayIntentBits, Partials, ChannelType, ActivityType } = require('discord.js');
const { joinVoiceChannel, createAudioPlayer, createAudioResource, VoiceConnectionStatus, AudioPlayerStatus, StreamType, getVoiceConnection, entersState, EndBehaviorType, NoSubscriberBehavior } = require('@discordjs/voice');
const OpusScript = require('opusscript');
const bundledFfmpegPath = require('ffmpeg-static');
let autoUpdater = null;
try {
  ({ autoUpdater } = require('electron-updater'));
} catch {}

let mainWindow;
let tray = null;
let isQuitting = false;
let client;
let voiceConnections = new Map();
let audioPlayers = new Map();
let microphoneStreams = new Map();
let activeSoundboards = new Map();
let soundDurationCache = new Map();
let activeAudioStreams = new Set();
let voiceSelfMute = false;
let voiceSelfDeaf = false;
let voiceHQAudio = { enabled: true, bitrate: 512000, stereo: true, freq: 48000, musicMode: false };
let audioBuffers = new Map(); // userId -> { chunks: [], timer }
const AUDIO_BUFFER_MS = 40; // lower latency while keeping IPC overhead reasonable
let powerSaveBlockerId = null;
let priorityWatchdogTimer = null;

function getFfmpegPath() {
  const candidates = [];
  if (bundledFfmpegPath) {
    candidates.push(String(bundledFfmpegPath).replace('app.asar', 'app.asar.unpacked'));
    candidates.push(bundledFfmpegPath);
  }
  if (process.resourcesPath) {
    candidates.push(path.join(process.resourcesPath, 'app.asar.unpacked', 'node_modules', 'ffmpeg-static', 'ffmpeg.exe'));
    candidates.push(path.join(process.resourcesPath, 'node_modules', 'ffmpeg-static', 'ffmpeg.exe'));
  }
  for (const candidate of candidates) {
    try {
      if (String(candidate).includes('app.asar' + path.sep) && !String(candidate).includes('app.asar.unpacked')) continue;
      if (candidate && fs.existsSync(candidate)) return candidate;
    } catch {}
  }
  return bundledFfmpegPath || 'ffmpeg';
}

function setProcessHighPriority(pid = process.pid) {
  if (process.platform !== 'win32' || !pid) return;
  try {
    spawn('powershell.exe', [
      '-NoProfile',
      '-ExecutionPolicy', 'Bypass',
      '-Command',
      `try { (Get-Process -Id ${Number(pid)}).PriorityClass = 'High' } catch {}`,
    ], { windowsHide: true, stdio: 'ignore' }).unref();
  } catch {}
}

function setBotCordProcessPriorities() {
  if (process.platform !== 'win32') return;
  try {
    const exe = path.basename(process.execPath).replace(/'/g, "''");
    const root = String(process.execPath).replace(/\\/g, '\\\\').replace(/'/g, "''");
    spawn('powershell.exe', [
      '-NoProfile',
      '-ExecutionPolicy', 'Bypass',
      '-Command',
      `$name='${exe}'; $root='${root}'; Get-CimInstance Win32_Process | Where-Object { ($_.Name -eq $name) -or ($_.CommandLine -like '*BotCord*') -or ($_.CommandLine -like '*botcord*') -or ($_.CommandLine -like "*$root*") } | ForEach-Object { try { (Get-Process -Id $_.ProcessId -ErrorAction Stop).PriorityClass = 'High' } catch {} }`,
    ], { windowsHide: true, stdio: 'ignore' }).unref();
  } catch {}
}

function startPriorityWatchdog() {
  setBotCordProcessPriorities();
  if (priorityWatchdogTimer) return;
  priorityWatchdogTimer = setInterval(setBotCordProcessPriorities, 5000);
  try { priorityWatchdogTimer.unref?.(); } catch {}
}

app.commandLine.appendSwitch('disable-background-timer-throttling');
app.commandLine.appendSwitch('disable-renderer-backgrounding');
app.commandLine.appendSwitch('disable-backgrounding-occluded-windows');
app.commandLine.appendSwitch('disable-features', 'CalculateNativeWinOcclusion,IntensiveWakeUpThrottling');
app.commandLine.appendSwitch('autoplay-policy', 'no-user-gesture-required');
app.commandLine.appendSwitch('disable-background-media-suspend');
app.commandLine.appendSwitch('disable-ipc-flooding-protection');

function sendUpdateStatus(status, detail = '') {
  try {
    mainWindow?.webContents.send('update-status', { status, detail });
  } catch {}
}

function setupAutoUpdater() {
  if (!autoUpdater || !app.isPackaged) return;
  autoUpdater.autoDownload = true;
  autoUpdater.autoInstallOnAppQuit = true;
  autoUpdater.allowPrerelease = false;
  autoUpdater.on('checking-for-update', () => sendUpdateStatus('checking'));
  autoUpdater.on('update-available', (info) => sendUpdateStatus('available', info?.version || ''));
  autoUpdater.on('update-not-available', () => sendUpdateStatus('none'));
  autoUpdater.on('download-progress', (progress) => {
    const percent = Number.isFinite(progress?.percent) ? Math.round(progress.percent) : 0;
    sendUpdateStatus('downloading', String(percent));
  });
  autoUpdater.on('update-downloaded', (info) => {
    sendUpdateStatus('ready', info?.version || '');
    if (Notification.isSupported()) {
      const notification = new Notification({
        title: 'BotCord update ready',
        body: 'Restart BotCord to install the newest version.',
        silent: true,
      });
      notification.on('click', () => {
        isQuitting = true;
        autoUpdater.quitAndInstall(false, true);
      });
      notification.show();
    }
  });
  autoUpdater.on('error', (error) => sendUpdateStatus('error', error?.message || String(error || 'Update failed')));
  setTimeout(() => autoUpdater.checkForUpdates().catch((error) => sendUpdateStatus('error', error?.message || String(error))), 12000);
}

function getTokenPath() {
  return path.join(app.getPath('userData'), 'discord-token.bin');
}

function saveToken(token) {
  if (!safeStorage.isEncryptionAvailable()) {
    throw new Error('Secure token storage is unavailable');
  }
  fs.writeFileSync(getTokenPath(), safeStorage.encryptString(token), { mode: 0o600 });
}

function loadToken() {
  try {
    const tokenPath = getTokenPath();
    if (!fs.existsSync(tokenPath) || !safeStorage.isEncryptionAvailable()) return null;
    return safeStorage.decryptString(fs.readFileSync(tokenPath));
  } catch {
    return null;
  }
}

function getPresencePath() {
  return path.join(app.getPath('userData'), 'presence.json');
}

function loadSavedStatus() {
  try {
    const status = JSON.parse(fs.readFileSync(getPresencePath(), 'utf8')).status;
    return ['online', 'idle', 'dnd', 'invisible'].includes(status) ? status : 'online';
  } catch {
    return 'online';
  }
}

function saveStatus(status) {
  fs.writeFileSync(getPresencePath(), JSON.stringify({ status }), 'utf8');
}

function getAudioPrefsPath() {
  return path.join(app.getPath('userData'), 'audio-preferences.json');
}

function loadAudioPrefs() {
  try {
    return JSON.parse(fs.readFileSync(getAudioPrefsPath(), 'utf8'));
  } catch {
    return {};
  }
}

function saveAudioPrefs(prefs) {
  fs.writeFileSync(getAudioPrefsPath(), JSON.stringify(prefs, null, 2), 'utf8');
}

function getKeybindsPath() {
  return path.join(app.getPath('userData'), 'keybinds.json');
}

function loadKeybinds() {
  try {
    return JSON.parse(fs.readFileSync(getKeybindsPath(), 'utf8'));
  } catch {
    return {};
  }
}

function saveKeybindsToFile(keybinds) {
  fs.writeFileSync(getKeybindsPath(), JSON.stringify(keybinds, null, 2), 'utf8');
}

function createWindow() {
  mainWindow = new BrowserWindow({
    width: 1280,
    height: 800,
    minWidth: 940,
    minHeight: 500,
    frame: true,
    titleBarStyle: 'hidden',
    titleBarOverlay: {
      color: '#1e1f22',
      symbolColor: '#949ba4',
      height: 32,
    },
    icon: path.join(__dirname, 'icon.ico'),
    backgroundColor: '#313338',
    webPreferences: {
      preload: path.join(__dirname, 'preload.js'),
      contextIsolation: true,
      nodeIntegration: false,
      backgroundThrottling: false,
    },
  });
  mainWindow.loadFile('index.html');
  mainWindow.on('close', (event) => {
    if (isQuitting) return;
    event.preventDefault();
    createTray();
    mainWindow.hide();
  });

  mainWindow.webContents.setWindowOpenHandler(({ url }) => {
    shell.openExternal(url);
    return { action: 'deny' };
  });
  mainWindow.webContents.on('will-navigate', (event, url) => {
    if (!url.startsWith('file://')) {
      event.preventDefault();
      shell.openExternal(url);
    }
  });
}

app.whenReady().then(() => {
  setProcessHighPriority();
  startPriorityWatchdog();
  if (powerSaveBlockerId === null || !powerSaveBlocker.isStarted(powerSaveBlockerId)) {
    powerSaveBlockerId = powerSaveBlocker.start('prevent-app-suspension');
  }
  createWindow();
  createTray();
  setupAutoUpdater();
});
app.on('before-quit', () => {
  if (powerSaveBlockerId !== null && powerSaveBlocker.isStarted(powerSaveBlockerId)) {
    powerSaveBlocker.stop(powerSaveBlockerId);
  }
});
app.on('window-all-closed', () => {
  if (isQuitting) app.quit();
});
app.on('will-quit', () => {
  if (priorityWatchdogTimer) {
    clearInterval(priorityWatchdogTimer);
    priorityWatchdogTimer = null;
  }
  if (tray) { tray.destroy(); tray = null; }
});

ipcMain.on('window-minimize', () => mainWindow?.minimize());
ipcMain.on('window-maximize', () => {
  if (mainWindow?.isMaximized()) mainWindow.unmaximize();
  else mainWindow?.maximize();
});
ipcMain.on('window-close', () => {
  if (!isQuitting) {
    createTray();
    mainWindow?.hide();
  } else {
    mainWindow?.close();
  }
});

ipcMain.handle('show-notification', async (_e, title, body) => {
  if (!Notification.isSupported()) return false;
  const notification = new Notification({ title, body, silent: false });
  notification.on('click', () => {
    if (!mainWindow) return;
    if (mainWindow.isMinimized()) mainWindow.restore();
    mainWindow.show();
    mainWindow.focus();
  });
  notification.show();
  return true;
});

ipcMain.handle('check-for-updates', async () => {
  if (!autoUpdater || !app.isPackaged) return { error: 'Updates only work in the installed app.' };
  try {
    const result = await autoUpdater.checkForUpdates();
    return { success: true, version: result?.updateInfo?.version || null };
  } catch (error) {
    return { error: error.message };
  }
});

// ── Login ──
async function loginWithToken(token, rememberToken = false) {
  if (client) { try { client.destroy(); } catch {} }
  const status = loadSavedStatus();
  client = new Client({
    intents: [
      GatewayIntentBits.Guilds,
      GatewayIntentBits.GuildMessages,
      GatewayIntentBits.GuildMembers,
      GatewayIntentBits.MessageContent,
      GatewayIntentBits.DirectMessages,
      GatewayIntentBits.DirectMessageTyping,
      GatewayIntentBits.GuildPresences,
      GatewayIntentBits.GuildVoiceStates,
      GatewayIntentBits.GuildMessageReactions,
    ],
    partials: [Partials.Channel, Partials.Message, Partials.User, Partials.Reaction],
    presence: { status },
  });

  return new Promise((resolve, reject) => {
    const timeout = setTimeout(() => reject(new Error('Login timed out')), 15000);
    client.once('ready', async () => {
      clearTimeout(timeout);
      setupListeners();
      if (rememberToken) saveToken(token);
      resolve({
        id: client.user.id,
        username: client.user.username,
        discriminator: client.user.discriminator,
        avatar: client.user.displayAvatarURL({ size: 128 }),
        globalName: client.user.globalName,
        status,
      });
    });
    client.login(token).catch((err) => { clearTimeout(timeout); reject(err); });
  });
}

ipcMain.handle('login', async (_e, token) => {
  return loginWithToken(token, true);
});

ipcMain.handle('auto-login', async () => {
  const token = loadToken();
  if (!token) return null;
  return loginWithToken(token, false);
});

ipcMain.handle('logout', async () => {
  if (client) {
    try { client.destroy(); } catch {}
    client = null;
  }
  try { fs.unlinkSync(getTokenPath()); } catch {}
  return true;
});

function setupListeners() {
  client.on('messageCreate', async (msg) => {
    const serialized = serializeMessage(msg);
    await hydrateReferencedMessage(serialized, msg);
    mainWindow?.webContents.send('message-create', serialized);
    if (msg.author.id !== client.user.id) {
      mainWindow?.webContents.send('notification-sound', {
        type: msg.mentions.has(client.user) ? 'mention' : 'message',
        mentionsMe: msg.mentions.has(client.user),
        channelId: msg.channelId,
        guildId: msg.guild?.id || null,
      });
    }
  });
  client.on('messageUpdate', async (_old, msg) => {
    if (msg.partial) return;
    const serialized = serializeMessage(msg);
    await hydrateReferencedMessage(serialized, msg);
    mainWindow?.webContents.send('message-update', serialized);
  });
  client.on('messageDelete', (msg) => {
    mainWindow?.webContents.send('message-delete', { id: msg.id, channelId: msg.channelId });
  });
  client.on('typingStart', (typing) => {
    mainWindow?.webContents.send('typing-start', {
      channelId: typing.channel.id,
      userId: typing.user?.id,
      username: typing.user?.username,
    });
  });
  client.on('messageReactionAdd', (reaction, user) => sendReactionUpdate(reaction, user).catch(() => {}));
  client.on('messageReactionRemove', (reaction, user) => sendReactionUpdate(reaction, user).catch(() => {}));
  client.on('voiceStateUpdate', (oldState, newState) => {
    if (newState.member?.id === client.user.id && newState.channelId) {
      const connection = voiceConnections.get(newState.guild.id);
      const player = audioPlayers.get(newState.guild.id);
      if (connection && player) connection.subscribe(player);
    }
    mainWindow?.webContents.send('voice-state-update', {
      guildId: newState.guild.id,
      channelId: newState.channelId,
      channelName: newState.channel?.name || null,
      oldChannelId: oldState.channelId,
      userId: newState.member?.id,
      username: newState.member?.user?.username,
      avatar: newState.member?.displayAvatarURL({ size: 64 }),
      selfMute: newState.selfMute,
      selfDeaf: newState.selfDeaf,
      serverMute: newState.serverMute,
      serverDeaf: newState.serverDeaf,
    });
  });
}

async function sendReactionUpdate(reaction, user) {
  if (reaction.partial) {
    try { reaction = await reaction.fetch(); } catch {}
  }
  let message = reaction.message;
  if (message?.partial) {
    try { message = await message.fetch(); } catch {}
  }
  const emojiKey = reaction.emoji.id || reaction.emoji.name;
  let accurateReaction = reaction;
  try {
    if (message?.reactions?.cache) {
      accurateReaction = message.reactions.cache.find((r) => (r.emoji.id || r.emoji.name) === emojiKey) || reaction;
    }
  } catch {}
  mainWindow?.webContents.send('reaction-update', {
    messageId: message?.id || reaction.message.id,
    channelId: message?.channelId || reaction.message.channelId,
    emoji: accurateReaction.emoji.name,
    emojiId: accurateReaction.emoji.id,
    animated: accurateReaction.emoji.animated,
    count: accurateReaction.count || 0,
    userId: user.id,
    me: user.id === client.user.id,
  });
}

function getUserFlagNames(user) {
  try {
    if (user?.flags?.toArray) return user.flags.toArray();
    if (user?.flags?.bitfield && user.flags.constructor?.Flags) {
      return Object.entries(user.flags.constructor.Flags)
        .filter(([, bit]) => (BigInt(user.flags.bitfield) & BigInt(bit)) !== 0n)
        .map(([name]) => name);
    }
  } catch {}
  return [];
}

function serializeUserBadges(user, member = null) {
  const flags = new Set(getUserFlagNames(user));
  const badges = [];
  const add = (id, label, icon, color = '#5865f2') => {
    if (!badges.some((b) => b.id === id)) badges.push({ id, label, icon, color });
  };

  if (flags.has('Staff')) add('staff', 'Discord Staff', 'STAFF', '#5865f2');
  if (flags.has('Partner')) add('partner', 'Partnered Server Owner', 'PARTNER', '#5865f2');
  if (flags.has('CertifiedModerator')) add('moderator', 'Discord Moderator Programs Alumni', 'MOD', '#5865f2');
  if (flags.has('Hypesquad')) add('hypesquad', 'HypeSquad Events', 'HYPE', '#f47fff');
  if (flags.has('HypeSquadOnlineHouse1')) add('bravery', 'HypeSquad Bravery', 'BRAVERY', '#9c84ef');
  if (flags.has('HypeSquadOnlineHouse2')) add('brilliance', 'HypeSquad Brilliance', 'BRILLIANCE', '#f47fff');
  if (flags.has('HypeSquadOnlineHouse3')) add('balance', 'HypeSquad Balance', 'BALANCE', '#45ddc0');
  if (flags.has('BugHunterLevel1')) add('bug_hunter_1', 'Bug Hunter', 'BUG', '#3ba55d');
  if (flags.has('BugHunterLevel2')) add('bug_hunter_2', 'Golden Bug Hunter', 'BUG+', '#faa61a');
  if (flags.has('PremiumEarlySupporter') || flags.has('EarlySupporter')) add('early_supporter', 'Early Supporter', 'EARLY', '#f47fff');
  if (flags.has('VerifiedDeveloper')) add('early_developer', 'Early Verified Bot Developer', 'DEV', '#5865f2');
  if (flags.has('ActiveDeveloper')) add('active_developer', 'Active Developer', 'ACTIVE', '#5865f2');
  if (flags.has('VerifiedBot')) add('verified_bot', 'Verified Bot', 'BOT', '#5865f2');
  if (member?.premiumSinceTimestamp || member?.premiumSince) add('server_booster', 'Server Booster', 'BOOST', '#f47fff');
  if (user?.bot && !badges.some((b) => b.id === 'verified_bot')) add('bot', 'Bot', 'BOT', '#5865f2');

  return badges;
}

function serializeMessage(msg) {
  return {
    id: msg.id,
    content: msg.content,
    channelId: msg.channel.id,
    guildId: msg.guild?.id || null,
    author: {
      id: msg.author.id,
      username: msg.author.username,
      displayName: msg.member?.displayName || msg.author.globalName || msg.author.username,
      color: msg.member?.displayHexColor && msg.member.displayHexColor !== '#000000'
        ? msg.member.displayHexColor
        : null,
      discriminator: msg.author.discriminator,
      avatar: msg.author.displayAvatarURL({ size: 64 }),
      bot: msg.author.bot,
      globalName: msg.author.globalName,
      badges: serializeUserBadges(msg.author, msg.member),
    },
    timestamp: msg.createdTimestamp,
    editedTimestamp: msg.editedTimestamp,
    deletable: msg.deletable,
    attachments: msg.attachments.map((a) => ({
      id: a.id, url: a.url, name: a.name,
      contentType: a.contentType, size: a.size,
      width: a.width, height: a.height,
    })),
    embeds: msg.embeds.map((e) => ({
      title: e.title, description: e.description, url: e.url,
      color: e.color, thumbnail: e.thumbnail?.url,
      image: e.image?.url, fields: e.fields,
      video: e.video ? { url: e.video.url || e.video.proxyURL, width: e.video.width, height: e.video.height } : null,
      provider: e.provider?.name || null,
      type: e.data?.type || null,
    })),
    reactions: msg.reactions?.cache.map((r) => ({
      emoji: r.emoji.name,
      emojiId: r.emoji.id,
      animated: r.emoji.animated,
      count: r.count,
      me: r.me,
    })) || [],
    referencedMessage: msg.reference ? {
      messageId: msg.reference.messageId,
      channelId: msg.reference.channelId,
      guildId: msg.reference.guildId,
    } : null,
    referencedMessageContent: null,
    type: msg.type,
  };
}

// ── Guilds / Channels ──
async function hydrateReferencedMessage(serialized, msg) {
  if (!serialized?.referencedMessage?.messageId || serialized.referencedMessageContent) return serialized;
  try {
    const refChannelId = serialized.referencedMessage.channelId || msg.channelId;
    const refChannel = client?.channels.cache.get(refChannelId) || msg.channel;
    if (!refChannel?.messages?.fetch) return serialized;
    const ref = await refChannel.messages.fetch(serialized.referencedMessage.messageId);
    serialized.referencedMessageContent = {
      content: ref.content?.substring(0, 200),
      author: {
        username: ref.author.username,
        displayName: ref.member?.displayName || ref.author.globalName || ref.author.username,
        avatar: ref.author.displayAvatarURL({ size: 32 }),
        color: ref.member?.displayHexColor && ref.member.displayHexColor !== '#000000'
          ? ref.member.displayHexColor
          : null,
      },
      attachments: ref.attachments.size > 0,
      embeds: ref.embeds.length > 0,
    };
  } catch {}
  return serialized;
}

ipcMain.handle('get-guilds', async () => {
  if (!client) return [];
  return client.guilds.cache.map((g) => ({
    id: g.id, name: g.name,
    icon: g.iconURL({ size: 64 }),
    memberCount: g.memberCount,
  }));
});

ipcMain.handle('get-channels', async (_e, guildId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return [];
  return guild.channels.cache
    .filter((c) => [ChannelType.GuildText, ChannelType.GuildVoice, ChannelType.GuildCategory, ChannelType.GuildAnnouncement, ChannelType.GuildForum, ChannelType.GuildStageVoice].includes(c.type))
    .sort((a, b) => a.rawPosition - b.rawPosition)
    .map((c) => {
      const data = {
        id: c.id, name: c.name, type: c.type,
        parentId: c.parentId, position: c.rawPosition,
        voiceMembers: [],
      };
      if (c.type === ChannelType.GuildVoice || c.type === ChannelType.GuildStageVoice) {
        data.voiceMembers = c.members.map((m) => ({
          id: m.id,
          username: m.user.username,
          displayName: m.displayName,
          avatar: m.displayAvatarURL({ size: 64 }),
          selfMute: m.voice.selfMute,
          selfDeaf: m.voice.selfDeaf,
          serverMute: m.voice.serverMute,
          serverDeaf: m.voice.serverDeaf,
          streaming: m.voice.streaming,
          video: m.voice.selfVideo,
        }));
      }
      return data;
    });
});

// ── Messages ──
ipcMain.handle('get-messages', async (_e, channelId, before) => {
  const channel = client?.channels.cache.get(channelId);
  if (!channel || !channel.isTextBased()) return [];
  const opts = { limit: 100 };
  if (before) opts.before = before;
  const messages = await channel.messages.fetch(opts);
  const result = [];
  for (const msg of messages.values()) {
    const s = serializeMessage(msg);
    await hydrateReferencedMessage(s, msg);
    result.push(s);
  }
  return result.reverse();
});

ipcMain.handle('send-message', async (_e, channelId, content, replyToId) => {
  const channel = client?.channels.cache.get(channelId);
  if (!channel || !channel.isTextBased()) return null;
  const opts = { content };
  if (replyToId) {
    opts.reply = { messageReference: replyToId, failIfNotExists: false };
  }
  const msg = await channel.send(opts);
  const serialized = serializeMessage(msg);
  await hydrateReferencedMessage(serialized, msg);
  return serialized;
});

ipcMain.handle('send-typing', async (_e, channelId) => {
  const channel = client?.channels.cache.get(channelId);
  if (!channel || !channel.isTextBased()) return false;
  await channel.sendTyping();
  return true;
});

ipcMain.handle('send-files', async (_e, channelId, content, replyToId) => {
  const channel = client?.channels.cache.get(channelId);
  if (!channel || !channel.isTextBased()) return null;
  const result = await dialog.showOpenDialog(mainWindow, {
    properties: ['openFile', 'multiSelections'],
    filters: [
      { name: 'Images and Files', extensions: ['png', 'jpg', 'jpeg', 'gif', 'webp', 'bmp', 'mp4', 'mov', 'webm', 'mp3', 'wav', 'pdf', 'txt', 'zip'] },
      { name: 'All Files', extensions: ['*'] },
    ],
  });
  if (result.canceled || !result.filePaths.length) return null;
  const opts = {
    content: content || undefined,
    files: result.filePaths.map((filePath) => ({ attachment: filePath, name: path.basename(filePath) })),
  };
  if (replyToId) opts.reply = { messageReference: replyToId, failIfNotExists: false };
  const msg = await channel.send(opts);
  const serialized = serializeMessage(msg);
  await hydrateReferencedMessage(serialized, msg);
  return serialized;
});

ipcMain.handle('send-file-buffers', async (_e, channelId, content, replyToId, files) => {
  const channel = client?.channels.cache.get(channelId);
  if (!channel || !channel.isTextBased() || !Array.isArray(files) || !files.length) return null;
  const opts = {
    content: content || undefined,
    files: files.map((file) => ({
      attachment: Buffer.from(file.buffer),
      name: file.name || 'upload.bin',
    })),
  };
  if (replyToId) opts.reply = { messageReference: replyToId, failIfNotExists: false };
  const msg = await channel.send(opts);
  const serialized = serializeMessage(msg);
  await hydrateReferencedMessage(serialized, msg);
  return serialized;
});

ipcMain.handle('edit-message', async (_e, channelId, messageId, newContent) => {
  const channel = client?.channels.cache.get(channelId);
  if (!channel) return null;
  const msg = await channel.messages.fetch(messageId);
  if (msg.author.id !== client.user.id) return null;
  const edited = await msg.edit(newContent);
  return serializeMessage(edited);
});

ipcMain.handle('delete-message', async (_e, channelId, messageId) => {
  const channel = client?.channels.cache.get(channelId);
  if (!channel) return false;
  const msg = await channel.messages.fetch(messageId);
  await msg.delete();
  return true;
});

ipcMain.handle('add-reaction', async (_e, channelId, messageId, emoji) => {
  const channel = client?.channels.cache.get(channelId);
  if (!channel) return false;
  const msg = await channel.messages.fetch(messageId);
  await msg.react(emoji);
  return true;
});

ipcMain.handle('remove-reaction', async (_e, channelId, messageId, emoji) => {
  const channel = client?.channels.cache.get(channelId);
  if (!channel) return false;
  const msg = await channel.messages.fetch(messageId);
  const emojiId = String(emoji).match(/:(\d{15,25})$/)?.[1] || String(emoji).match(/^(\d{15,25})$/)?.[1];
  const reaction = msg.reactions.cache.find((r) => emojiId ? r.emoji.id === emojiId : r.emoji.name === emoji);
  if (reaction) await reaction.users.remove(client.user.id);
  return true;
});

ipcMain.handle('fetch-reply-message', async (_e, channelId, messageId) => {
  try {
    const channel = client?.channels.cache.get(channelId);
    if (!channel) return null;
    const msg = await channel.messages.fetch(messageId);
    return {
      content: msg.content?.substring(0, 200),
      author: { username: msg.author.username, displayName: msg.member?.displayName || msg.author.globalName || msg.author.username, avatar: msg.author.displayAvatarURL({ size: 32 }) },
      attachments: msg.attachments.size > 0,
      embeds: msg.embeds.length > 0,
    };
  } catch { return null; }
});

// ── DMs ──
ipcMain.handle('get-dm-channels', async () => {
  if (!client) return [];
  return client.channels.cache
    .filter((c) => c.type === ChannelType.DM)
    .map((c) => ({
      id: c.id, recipientId: c.recipient?.id,
      recipientName: c.recipient?.username || 'Unknown',
      recipientAvatar: c.recipient?.displayAvatarURL({ size: 64 }),
    }));
});

ipcMain.handle('create-dm', async (_e, userId) => {
  const user = await client?.users.fetch(userId);
  if (!user) return null;
  const dm = await user.createDM();
  return {
    id: dm.id, recipientId: user.id,
    recipientName: user.username,
    recipientAvatar: user.displayAvatarURL({ size: 64 }),
  };
});

// ── Members ──
ipcMain.handle('get-guild-members', async (_e, guildId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return [];
  let members;
  try {
    members = await guild.members.fetch({ withPresences: true, time: 120_000 });
  } catch {
    members = guild.members.cache;
  }
  return members.map((m) => ({
      id: m.id, username: m.user.username,
      displayName: m.displayName,
      avatar: m.displayAvatarURL({ size: 64 }),
      status: m.presence?.status || 'offline',
      bot: m.user.bot,
      badges: serializeUserBadges(m.user, m),
      joinedAt: m.joinedTimestamp,
      createdAt: m.user.createdTimestamp,
      premiumSince: m.premiumSinceTimestamp,
      roles: m.roles.cache
        .filter((r) => r.id !== guild.id)
        .sort((a, b) => b.position - a.position)
        .map((r) => ({
          id: r.id,
          name: r.name,
          color: r.hexColor,
          hoist: r.hoist,
          position: r.position,
        })),
    }));
});

// ── User Profile ──
ipcMain.handle('get-user-profile', async (_e, userId, guildId) => {
  try {
    const user = await client.users.fetch(userId, { force: true });
    let member = null;
    let roles = [];
    let nickname = null;
    if (guildId) {
      const guild = client.guilds.cache.get(guildId);
      if (guild) {
        try {
          member = await guild.members.fetch(userId);
          nickname = member.nickname;
          roles = member.roles.cache
            .filter((r) => r.id !== guild.id)
            .sort((a, b) => b.position - a.position)
            .map((r) => ({ id: r.id, name: r.name, color: r.hexColor }));
        } catch {}
      }
    }

    const mutualGuilds = client.guilds.cache
      .filter((g) => g.members.cache.has(userId))
      .map((g) => ({ id: g.id, name: g.name, icon: g.iconURL({ size: 32 }) }));

    const presence = member?.presence;
    let customStatus = null;
    let activity = null;
    if (presence?.activities) {
      for (const act of presence.activities) {
        if (act.type === 4) {
          customStatus = { text: act.state, emoji: act.emoji?.name || null };
        } else {
          const typeNames = ['Playing', 'Streaming', 'Listening to', 'Watching', 'Custom', 'Competing in'];
          activity = { type: typeNames[act.type] || 'Playing', name: act.name, details: act.details, state: act.state };
        }
      }
    }

    return {
      id: user.id,
      username: user.username,
      globalName: user.globalName,
      discriminator: user.discriminator,
      avatar: user.displayAvatarURL({ size: 256 }),
      banner: user.bannerURL?.({ size: 512 }) || null,
      bannerColor: user.hexAccentColor || null,
      bot: user.bot,
      createdAt: user.createdTimestamp,
      status: presence?.status || 'offline',
      customStatus,
      activity,
      nickname,
      badges: serializeUserBadges(user, member),
      roles,
      mutualGuilds,
    };
  } catch (e) {
    return null;
  }
});

// ── Bot Profile / Settings ──
ipcMain.handle('get-bot-user', async () => {
  if (!client?.user) return null;
  return {
    id: client.user.id,
    username: client.user.username,
    discriminator: client.user.discriminator,
    avatar: client.user.displayAvatarURL({ size: 256 }),
    banner: client.user.bannerURL?.({ size: 512 }) || null,
    globalName: client.user.globalName,
    bio: '',
    status: loadSavedStatus(),
  };
});

ipcMain.handle('set-username', async (_e, username) => {
  await client.user.setUsername(username);
  return { username: client.user.username };
});

ipcMain.handle('set-avatar', async () => {
  const result = await dialog.showOpenDialog(mainWindow, {
    properties: ['openFile'],
    filters: [{ name: 'Images', extensions: ['png', 'jpg', 'jpeg', 'gif', 'webp'] }],
  });
  if (result.canceled || !result.filePaths.length) return null;
  const filePath = result.filePaths[0];
  const data = fs.readFileSync(filePath);
  const base64 = `data:image/${path.extname(filePath).slice(1)};base64,${data.toString('base64')}`;
  await client.user.setAvatar(base64);
  return { avatar: client.user.displayAvatarURL({ size: 256, forceStatic: false }) };
});

ipcMain.handle('select-avatar', async () => {
  const result = await dialog.showOpenDialog(mainWindow, {
    properties: ['openFile'],
    filters: [{ name: 'Images', extensions: ['png', 'jpg', 'jpeg', 'gif', 'webp'] }],
  });
  if (result.canceled || !result.filePaths.length) return null;
  const filePath = result.filePaths[0];
  const data = fs.readFileSync(filePath);
  return `data:image/${path.extname(filePath).slice(1)};base64,${data.toString('base64')}`;
});

ipcMain.handle('confirm-avatar', async (_e, base64) => {
  try { await client.user.setAvatar(base64); return { avatar: client.user.displayAvatarURL({ size: 256, forceStatic: false }) }; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('select-banner', async () => {
  const result = await dialog.showOpenDialog(mainWindow, {
    properties: ['openFile'],
    filters: [{ name: 'Images', extensions: ['png', 'jpg', 'jpeg', 'gif', 'webp'] }],
  });
  if (result.canceled || !result.filePaths.length) return null;
  const filePath = result.filePaths[0];
  const data = fs.readFileSync(filePath);
  return `data:image/${path.extname(filePath).slice(1)};base64,${data.toString('base64')}`;
});

ipcMain.handle('confirm-banner', async (_e, base64) => {
  try { await client.user.setBanner(base64); return true; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('set-banner', async () => {
  const result = await dialog.showOpenDialog(mainWindow, {
    properties: ['openFile'],
    filters: [{ name: 'Images', extensions: ['png', 'jpg', 'jpeg', 'gif', 'webp'] }],
  });
  if (result.canceled || !result.filePaths.length) return null;
  const filePath = result.filePaths[0];
  const data = fs.readFileSync(filePath);
  const base64 = `data:image/${path.extname(filePath).slice(1)};base64,${data.toString('base64')}`;
  try { await client.user.setBanner(base64); return true; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('remove-banner', async () => {
  try { await client.user.setBanner(null); return true; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('set-status', async (_e, status) => {
  if (!['online', 'idle', 'dnd', 'invisible'].includes(status)) {
    throw new Error('Invalid status');
  }
  if (!client?.isReady()) throw new Error('Discord is not connected');
  client.user.setStatus(status);
  saveStatus(status);
  return { status: client.presence.status };
});

ipcMain.handle('set-activity', async (_e, type, name) => {
  const typeMap = {
    playing: ActivityType.Playing,
    streaming: ActivityType.Streaming,
    listening: ActivityType.Listening,
    watching: ActivityType.Watching,
    competing: ActivityType.Competing,
    custom: ActivityType.Custom,
  };
  await client.user.setPresence({
    status: loadSavedStatus(),
    activities: name ? [{ name, type: typeMap[type] || ActivityType.Playing }] : [],
  });
  return true;
});

// ── Voice ──
function flushAudioBuffer(userId) {
  const entry = audioBuffers.get(userId);
  if (!entry || !entry.chunks.length || !mainWindow || mainWindow.isDestroyed()) return;
  const totalLen = entry.chunks.reduce((s, c) => s + c.length, 0);
  const merged = Buffer.concat(entry.chunks, totalLen);
  entry.chunks = [];
  mainWindow.webContents.send(
    'voice-pcm',
    merged.buffer.slice(merged.byteOffset, merged.byteOffset + merged.byteLength),
    userId,
  );
}

function subscribeToVoiceAudio(connection, guildId) {
  const receiver = connection.receiver;

  receiver.speaking.on('start', (userId) => {
    if (activeAudioStreams.has(userId)) return;
    activeAudioStreams.add(userId);
    mainWindow?.webContents.send('voice-speaking', { guildId, userId, speaking: true });

    const opusStream = receiver.subscribe(userId, {
      end: { behavior: EndBehaviorType.AfterSilence, duration: 500 },
    });

    const decoder = new OpusScript(48000, 2, OpusScript.Application.AUDIO);

    if (!audioBuffers.has(userId)) {
      audioBuffers.set(userId, { chunks: [], timer: null });
    }
    const entry = audioBuffers.get(userId);
    if (entry.timer) clearInterval(entry.timer);
    entry.timer = setInterval(() => flushAudioBuffer(userId), AUDIO_BUFFER_MS);

    opusStream.on('data', (opusPacket) => {
      if (voiceSelfDeaf) return;
      try {
        const pcmChunk = decoder.decode(opusPacket, 960);
        if (pcmChunk?.length) entry.chunks.push(Buffer.from(pcmChunk));
      } catch {
        // UDP voice can occasionally deliver a malformed/late packet.
        // Dropping one packet is preferable to crashing the main process.
      }
    });

    let cleanedUp = false;
    const cleanup = () => {
      if (cleanedUp) return;
      cleanedUp = true;
      activeAudioStreams.delete(userId);
      mainWindow?.webContents.send('voice-speaking', { guildId, userId, speaking: false });
      const e = audioBuffers.get(userId);
      if (e) {
        flushAudioBuffer(userId);
        if (e.timer) clearInterval(e.timer);
        audioBuffers.delete(userId);
      }
      try { decoder.delete(); } catch {}
    };
    opusStream.on('end', cleanup);
    opusStream.on('close', cleanup);
    opusStream.on('error', cleanup);
  });
}

function cleanupAllAudio() {
  for (const guildId of activeSoundboards.keys()) {
    cleanupSoundboard(guildId, { resumeMic: false });
  }
  activeAudioStreams.clear();
  for (const [uid, entry] of audioBuffers) {
    if (entry.timer) clearInterval(entry.timer);
  }
  audioBuffers.clear();
}

function stopMicrophoneStream(guildId) {
  const entry = microphoneStreams.get(guildId);
  if (entry) {
    try { entry.stream?.end(); } catch {}
    try { entry.encoder?.delete?.(); } catch {}
    microphoneStreams.delete(guildId);
  }
}

function startMicrophoneStream(guildId) {
  const player = audioPlayers.get(guildId);
  if (!player) return false;
  stopMicrophoneStream(guildId);
  const stream = new PassThrough({ objectMode: true });
  const encoder = new OpusScript(
    48000,
    2,
    voiceHQAudio.musicMode ? OpusScript.Application.AUDIO : OpusScript.Application.VOIP,
  );
  microphoneStreams.set(guildId, {
    stream,
    encoder,
    pcmBuffer: Buffer.alloc(0),
    startedAt: Date.now(),
    lastPcmAt: 0,
    lastPacketAt: 0,
  });
  const resource = createAudioResource(stream, { inputType: StreamType.Opus });
  player.play(resource);
  return true;
}

function sendSoundpadState(guildId, state, extra = {}) {
  mainWindow?.webContents.send('soundpad-state', { guildId, state, ...extra });
}

function soundpadElapsedMs(entry) {
  if (!entry) return 0;
  if (entry.paused) return entry.offsetMs || 0;
  return (entry.offsetMs || 0) + Math.max(0, Date.now() - (entry.startedAt || Date.now()));
}

function safeFilterNumber(value, fallback, min, max) {
  const n = Number(value);
  if (!Number.isFinite(n)) return fallback;
  return Math.max(min, Math.min(max, n));
}

function probeSoundDurationMs(soundPath) {
  if (!soundPath) return Promise.resolve(0);
  if (soundDurationCache.has(soundPath)) return Promise.resolve(soundDurationCache.get(soundPath));
  return new Promise((resolve) => {
    let stderr = '';
    const ffmpeg = spawn(getFfmpegPath(), ['-hide_banner', '-i', soundPath], { windowsHide: true });
    ffmpeg.stderr?.on('data', (chunk) => { stderr += chunk.toString(); });
    const done = () => {
      const match = stderr.match(/Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)/);
      const ms = match
        ? Math.round(((Number(match[1]) * 3600) + (Number(match[2]) * 60) + Number(match[3])) * 1000)
        : 0;
      soundDurationCache.set(soundPath, ms);
      resolve(ms);
    };
    ffmpeg.on('close', done);
    ffmpeg.on('error', () => resolve(0));
  });
}

function buildSoundpadFilters(settings = {}) {
  const filters = [];
  const pitchOn = !!settings.pitch?.on;
  const pitchSemis = safeFilterNumber(settings.pitch?.val, 0, -24, 24);
  if (pitchOn && Math.abs(pitchSemis) > 0.01) {
    const rate = Math.pow(2, pitchSemis / 12);
    filters.push(`asetrate=48000*${rate.toFixed(5)}`, 'aresample=48000');
  }

  if (settings.enabled !== false && Array.isArray(settings.bands)) {
    for (const band of settings.bands.slice(0, 20)) {
      const freq = safeFilterNumber(band.freq, 1000, 20, 20000);
      const gain = safeFilterNumber(band.gain, 0, -30, 30);
      const q = safeFilterNumber(band.Q, 1, 0.1, 18);
      const type = String(band.type || 'peaking').toLowerCase();
      if (type === 'lowpass') filters.push(`lowpass=f=${freq.toFixed(2)}`);
      else if (type === 'highpass') filters.push(`highpass=f=${freq.toFixed(2)}`);
      else if (type === 'lowshelf') filters.push(`bass=f=${freq.toFixed(2)}:g=${gain.toFixed(2)}`);
      else if (type === 'highshelf') filters.push(`treble=f=${freq.toFixed(2)}:g=${gain.toFixed(2)}`);
      else filters.push(`equalizer=f=${freq.toFixed(2)}:t=q:w=${q.toFixed(2)}:g=${gain.toFixed(2)}`);
    }
  }

  if (settings.comp?.on) filters.push('acompressor=threshold=-18dB:ratio=3:attack=8:release=120:makeup=1.5');
  if (settings.tremolo?.on) {
    const speed = safeFilterNumber(settings.tremolo.speed, 5, 0.1, 20);
    const depth = safeFilterNumber(settings.tremolo.depth, 0.5, 0, 1);
    filters.push(`tremolo=f=${speed.toFixed(2)}:d=${depth.toFixed(2)}`);
  }
  if (settings.delay?.on) {
    const time = safeFilterNumber(settings.delay.time, 0.25, 0.02, 2) * 1000;
    const feedback = safeFilterNumber(settings.delay.feedback, 0.25, 0, 0.9);
    filters.push(`aecho=0.8:0.65:${time.toFixed(0)}:${feedback.toFixed(2)}`);
  } else if (settings.reverb?.on) {
    const room = safeFilterNumber(settings.reverb.room, 0.45, 0, 1);
    const wet = safeFilterNumber(settings.reverb.wet, 0.3, 0, 1);
    const damp = safeFilterNumber(settings.reverb.damp, 0.5, 0, 1);
    const dry = safeFilterNumber(settings.reverb.dry, 0.7, 0, 1);
    const delay1 = Math.round(18 + room * 32);
    const delay2 = Math.round(42 + room * 58);
    const decay1 = Math.min(0.22, Math.max(0.025, wet * 0.2));
    const decay2 = Math.min(0.16, Math.max(0.015, wet * 0.13));
    const lowpass = Math.round(12500 - damp * 6500);
    filters.push(`aecho=${Math.max(0.55, dry).toFixed(2)}:${Math.min(0.34, wet * 0.55).toFixed(2)}:${delay1}|${delay2}:${decay1.toFixed(3)}|${decay2.toFixed(3)}`, `lowpass=f=${lowpass}`);
  }

  const gain = safeFilterNumber(settings.gain, 1, 0, 4);
  const volume = safeFilterNumber(settings.volume, 1, 0, 2);
  const finalVolume = Math.max(0, Math.min(8, gain * volume));
  if (Math.abs(finalVolume - 1) > 0.001) filters.push(`volume=${finalVolume.toFixed(3)}`);
  return filters.join(',');
}

function clampInt16(value) {
  return Math.max(-32768, Math.min(32767, value | 0));
}

function createSoundpadLiveTransform(entry) {
  let carry = Buffer.alloc(0);
  entry.livePan = Number.isFinite(entry.livePan) ? entry.livePan : 0;
  entry.liveOrbitAngle = Number.isFinite(entry.liveOrbitAngle) ? entry.liveOrbitAngle : 0;
  return new Transform({
    transform(chunk, _encoding, callback) {
      const input = carry.length ? Buffer.concat([carry, chunk]) : chunk;
      const usable = input.length - (input.length % 4);
      carry = usable < input.length ? input.subarray(usable) : Buffer.alloc(0);
      if (usable <= 0) return callback();

      const output = Buffer.allocUnsafe(usable);
      const settings = entry.settings || {};
      const spatial = settings['8d'] || settings.spatial || {};
      const stereoMono = !!settings.stereo?.on;
      const targetPan = spatial?.on ? Math.max(-1, Math.min(1, safeFilterNumber(spatial.x, 0, -5, 5) / 5)) : 0;
      const targetDepth = spatial?.on ? Math.max(0, Math.min(1, Math.abs(safeFilterNumber(spatial.z, 0, -5, 5)) / 10)) : 0;
      const orbiting = !!(spatial?.on && spatial.orbit);
      const orbitSpeed = orbiting ? safeFilterNumber(spatial.speed, 0.3, 0.01, 4) : 0;
      const orbitDepth = orbiting ? safeFilterNumber(spatial.depth, 2, 0.1, 5) : safeFilterNumber(spatial.depth, 2, 0.1, 5);
      const orbitStep = orbiting ? (orbitSpeed * Math.PI * 2) / 48000 : 0;
      const baseWidthBoost = spatial?.on ? Math.max(0, Math.min(0.35, orbitDepth / 18 + targetDepth * 0.15)) : 0;

      for (let offset = 0; offset < usable; offset += 4) {
        let left = input.readInt16LE(offset);
        let right = input.readInt16LE(offset + 2);

        if (stereoMono) {
          const mono = (left + right) * 0.5;
          left = mono;
          right = mono;
        }

        let liveTargetPan = targetPan;
        let liveWidthBoost = baseWidthBoost;
        if (orbiting) {
          entry.liveOrbitAngle += orbitStep;
          if (entry.liveOrbitAngle > Math.PI * 2) entry.liveOrbitAngle -= Math.PI * 2;
          liveTargetPan = Math.max(-1, Math.min(1, (Math.sin(entry.liveOrbitAngle) * orbitDepth) / 5));
          liveWidthBoost = Math.max(0, Math.min(0.35, orbitDepth / 16 + Math.abs(Math.cos(entry.liveOrbitAngle)) * 0.08));
        }

        entry.livePan += (liveTargetPan - entry.livePan) * 0.08;
        const pan = entry.livePan;
        const leftGain = pan <= 0 ? 1 : 1 - pan;
        const rightGain = pan >= 0 ? 1 : 1 + pan;

        if (liveWidthBoost && !stereoMono) {
          const mid = (left + right) * 0.5;
          const side = (left - right) * (0.5 + liveWidthBoost);
          left = mid + side;
          right = mid - side;
        }

        output.writeInt16LE(clampInt16(left * leftGain), offset);
        output.writeInt16LE(clampInt16(right * rightGain), offset + 2);
      }

      callback(null, output);
    },
    flush(callback) {
      carry = Buffer.alloc(0);
      callback();
    },
  });
}

function cleanupSoundboard(guildId, { resumeMic = false, keepEntry = false } = {}) {
  const entry = activeSoundboards.get(guildId);
  if (!entry) return null;
  entry.intentionalStop = true;
  if (entry.idleHandler) {
    try { entry.player.off(AudioPlayerStatus.Idle, entry.idleHandler); } catch {}
  }
  try { entry.process?.kill?.('SIGKILL'); } catch {}
  try { entry.player.stop(true); } catch {}
  if (!keepEntry) activeSoundboards.delete(guildId);
  if (resumeMic && entry.wasMicActive) startMicrophoneStream(guildId);
  return entry;
}

async function startSoundboardPlayback(guildId, soundPath, settings = {}, offsetMs = 0, wasMicOverride = null, recoveryCount = 0) {
  const player = audioPlayers.get(guildId);
  if (!player) return { error: 'Not connected to voice' };
  const durationMs = await probeSoundDurationMs(soundPath);
  const previous = activeSoundboards.get(guildId);
  const wasMicActive = wasMicOverride ?? previous?.wasMicActive ?? microphoneStreams.has(guildId);
  cleanupSoundboard(guildId, { resumeMic: false });
  if (microphoneStreams.has(guildId)) stopMicrophoneStream(guildId);

  const args = [
    '-hide_banner', '-loglevel', 'error',
    '-ss', String(Math.max(0, offsetMs / 1000)),
    '-i', soundPath,
    '-vn',
    '-ac', '2',
    '-ar', '48000',
  ];
  const filters = buildSoundpadFilters(settings);
  if (filters) args.push('-af', filters);
  args.push('-f', 's16le', 'pipe:1');

  const ffmpeg = spawn(getFfmpegPath(), args, { windowsHide: true });
  setProcessHighPriority(ffmpeg.pid);
  setBotCordProcessPriorities();
  ffmpeg.stderr?.on('data', (chunk) => console.warn('soundpad ffmpeg:', chunk.toString().trim()));
  ffmpeg.on('error', (error) => {
    sendSoundpadState(guildId, 'error', { path: soundPath, error: error.message });
  });

  const entry = {
    player,
    process: ffmpeg,
    path: soundPath,
    settings,
    filterSignature: filters,
    offsetMs: Math.max(0, offsetMs),
    durationMs,
    startedAt: Date.now(),
    paused: false,
    wasMicActive,
    intentionalStop: false,
    recoveryCount,
    idleHandler: null,
  };
  const liveTransform = createSoundpadLiveTransform(entry);
  ffmpeg.stdout.pipe(liveTransform);
  const resource = createAudioResource(liveTransform, { inputType: StreamType.Raw });
  entry.idleHandler = () => {
    const current = activeSoundboards.get(guildId);
    if (current !== entry) return;
    const elapsedMs = soundpadElapsedMs(entry);
    const endedNaturally = !durationMs || elapsedMs >= durationMs - 1500;
    activeSoundboards.delete(guildId);
    try { ffmpeg.kill('SIGKILL'); } catch {}
    if (!entry.intentionalStop && !entry.paused && !endedNaturally && entry.recoveryCount < 3) {
      sendSoundpadState(guildId, 'playing', { path: soundPath, offsetMs: elapsedMs, durationMs });
      setTimeout(() => {
        if (activeSoundboards.has(guildId)) return;
        startSoundboardPlayback(guildId, soundPath, settings, elapsedMs, entry.wasMicActive, entry.recoveryCount + 1)
          .catch((error) => sendSoundpadState(guildId, 'error', { path: soundPath, error: error.message }));
      }, 120);
      return;
    }
    if (entry.wasMicActive) startMicrophoneStream(guildId);
    sendSoundpadState(guildId, 'ended', { path: soundPath, durationMs });
  };
  player.on(AudioPlayerStatus.Idle, entry.idleHandler);
  activeSoundboards.set(guildId, entry);
  player.play(resource);
  sendSoundpadState(guildId, 'playing', { path: soundPath, offsetMs: entry.offsetMs, durationMs });
  return { success: true, durationMs };
}

ipcMain.handle('join-voice', async (_e, guildId, channelId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return { error: 'Guild not found' };
  const channel = guild.channels.cache.get(channelId);
  if (!channel) return { error: 'Channel not found' };

  try {
    voiceSelfMute = false;
    voiceSelfDeaf = false;

    const connection = joinVoiceChannel({
      channelId: channel.id,
      guildId: guild.id,
      adapterCreator: guild.voiceAdapterCreator,
      selfDeaf: false,
      selfMute: false,
    });

    voiceConnections.set(guildId, connection);
    const player = createAudioPlayer({
      behaviors: {
        noSubscriber: NoSubscriberBehavior.Play,
      },
    });
    audioPlayers.set(guildId, player);
    connection.subscribe(player);
    player.on('error', (err) => {
      console.error('Voice mic player error:', err);
      stopMicrophoneStream(guildId);
    });

    await entersState(connection, VoiceConnectionStatus.Ready, 15_000);

    subscribeToVoiceAudio(connection, guildId);

    connection.on(VoiceConnectionStatus.Disconnected, async () => {
      try {
        // Muting, server moves, and network recovery can all pass through
        // Disconnected temporarily. Only clean up if Ready is not restored.
        await entersState(connection, VoiceConnectionStatus.Ready, 15_000);
      } catch {
        if (connection.state.status === VoiceConnectionStatus.Destroyed) return;
        cleanupAllAudio();
        connection.destroy();
        mainWindow?.webContents.send('voice-disconnected', { guildId, channelId });
        voiceConnections.delete(guildId);
        audioPlayers.delete(guildId);
        stopMicrophoneStream(guildId);
      }
    });

    return {
      success: true,
      channelId: channel.id,
      channelName: channel.name,
      guildId: guild.id,
    };
  } catch (err) {
    return { error: err.message };
  }
});

ipcMain.handle('leave-voice', async (_e, guildId) => {
  const connection = voiceConnections.get(guildId) || getVoiceConnection(guildId);
  if (connection) {
    cleanupAllAudio();
    stopMicrophoneStream(guildId);
    connection.destroy();
    voiceConnections.delete(guildId);
    audioPlayers.delete(guildId);
  }
  voiceSelfMute = false;
  voiceSelfDeaf = false;
  return true;
});

ipcMain.handle('start-microphone', async (_e, guildId) => {
  return startMicrophoneStream(guildId);
});

ipcMain.handle('set-hq-audio', async (_e, settings) => {
  voiceHQAudio = { ...voiceHQAudio, ...settings };
  return voiceHQAudio;
});

ipcMain.handle('get-hq-audio', async () => {
  return voiceHQAudio;
});

ipcMain.on('microphone-pcm', (_e, guildId, pcmBuffer) => {
  if (voiceSelfMute || voiceSelfDeaf) return;
  let entry = microphoneStreams.get(guildId);
  if ((!entry || !entry.stream || entry.stream.destroyed || !entry.encoder) && !activeSoundboards.has(guildId)) {
    startMicrophoneStream(guildId);
    entry = microphoneStreams.get(guildId);
  }
  if (!entry || !entry.stream || entry.stream.destroyed || !entry.encoder) return;
  entry.lastPcmAt = Date.now();
  entry.pcmBuffer = Buffer.concat([entry.pcmBuffer, Buffer.from(pcmBuffer)]);
  const frameBytes = 960 * 2 * 2; // 20ms, 48kHz, stereo, signed 16-bit little-endian
  while (entry.pcmBuffer.length >= frameBytes) {
    const frame = entry.pcmBuffer.subarray(0, frameBytes);
    entry.pcmBuffer = entry.pcmBuffer.subarray(frameBytes);
    try {
      const opusPacket = entry.encoder.encode(frame, 960);
      if (opusPacket?.length) {
        entry.stream.write(Buffer.from(opusPacket));
        entry.lastPacketAt = Date.now();
      }
    } catch (err) {
      console.error('Microphone Opus encode error:', err);
      entry.pcmBuffer = Buffer.alloc(0);
      break;
    }
  }
});

ipcMain.handle('get-microphone-health', async (_e, guildId) => {
  const entry = microphoneStreams.get(guildId);
  return {
    active: !!entry && !!entry.stream && !entry.stream.destroyed && !!entry.encoder,
    startedAt: entry?.startedAt || 0,
    lastPcmAt: entry?.lastPcmAt || 0,
    lastPacketAt: entry?.lastPacketAt || 0,
    bufferedBytes: entry?.pcmBuffer?.length || 0,
    selfMute: voiceSelfMute,
    selfDeaf: voiceSelfDeaf,
  };
});

ipcMain.handle('stop-microphone', async (_e, guildId) => {
  stopMicrophoneStream(guildId);
  return true;
});

ipcMain.handle('toggle-mute', async (_e, guildId) => {
  const connection = voiceConnections.get(guildId);
  if (!connection) return null;
  const guild = client?.guilds.cache.get(guildId);
  const channelId = guild?.members.me?.voice.channelId;
  if (!channelId) return null;

  voiceSelfMute = !voiceSelfMute;
  const started = connection.rejoin({ channelId, selfMute: voiceSelfMute, selfDeaf: voiceSelfDeaf });
  if (!started) return null;
  await entersState(connection, VoiceConnectionStatus.Ready, 15_000);
  const player = audioPlayers.get(guildId);
  if (player) connection.subscribe(player);
  return { selfMute: voiceSelfMute, selfDeaf: voiceSelfDeaf };
});

ipcMain.handle('toggle-deaf', async (_e, guildId) => {
  const connection = voiceConnections.get(guildId);
  if (!connection) return null;
  const guild = client?.guilds.cache.get(guildId);
  const channelId = guild?.members.me?.voice.channelId;
  if (!channelId) return null;

  voiceSelfDeaf = !voiceSelfDeaf;
  if (voiceSelfDeaf) voiceSelfMute = true;
  else voiceSelfMute = false;
  const started = connection.rejoin({ channelId, selfMute: voiceSelfMute, selfDeaf: voiceSelfDeaf });
  if (!started) return null;
  await entersState(connection, VoiceConnectionStatus.Ready, 15_000);
  const player = audioPlayers.get(guildId);
  if (player) connection.subscribe(player);
  return { selfMute: voiceSelfMute, selfDeaf: voiceSelfDeaf };
});

ipcMain.handle('get-voice-channel-members', async (_e, guildId, channelId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return [];
  const channel = guild.channels.cache.get(channelId);
  if (!channel) return [];
  return channel.members.map((m) => ({
    id: m.id, username: m.user.username,
    displayName: m.displayName,
    avatar: m.displayAvatarURL({ size: 64 }),
    selfMute: m.voice.selfMute,
    selfDeaf: m.voice.selfDeaf,
    serverMute: m.voice.serverMute,
    serverDeaf: m.voice.serverDeaf,
  }));
});

ipcMain.handle('get-voice-state', async (_e, guildId) => {
  const connection = voiceConnections.get(guildId);
  if (!connection) return null;
  const guild = client?.guilds.cache.get(guildId);
  const me = guild?.members.me;
  return {
    channelId: me?.voice.channelId,
    channelName: me?.voice.channel?.name,
    guildId,
    guildName: guild?.name,
    selfMute: me?.voice.selfMute || false,
    selfDeaf: me?.voice.selfDeaf || false,
  };
});

// ── Server Settings ──
ipcMain.handle('set-nickname', async (_e, guildId, nickname) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try { await guild.members.me.setNickname(nickname || null); return true; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('get-guild-info', async (_e, guildId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return null;
  return {
    id: guild.id, name: guild.name,
    icon: guild.iconURL({ size: 256 }),
    banner: guild.bannerURL({ size: 512 }),
    splash: guild.splashURL({ size: 512 }),
    memberCount: guild.memberCount,
    ownerId: guild.ownerId,
    description: guild.description,
    verificationLevel: guild.verificationLevel,
    explicitContentFilter: guild.explicitContentFilter,
    defaultMessageNotifications: guild.defaultMessageNotifications,
    systemChannelId: guild.systemChannelId,
    rulesChannelId: guild.rulesChannelId,
    publicUpdatesChannelId: guild.publicUpdatesChannelId,
    afkChannelId: guild.afkChannelId,
    afkTimeout: guild.afkTimeout,
    premiumTier: guild.premiumTier,
    premiumSubscriptionCount: guild.premiumSubscriptionCount,
    vanityURLCode: guild.vanityURLCode,
    features: guild.features,
    myNickname: guild.members.me?.nickname || '',
    createdAt: guild.createdTimestamp,
  };
});

ipcMain.handle('get-guild-events', async (_e, guildId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return [];
  try {
    const events = await guild.scheduledEvents.fetch();
    return events.map((event) => ({
      id: event.id,
      name: event.name,
      description: event.description || '',
      image: event.coverImageURL({ size: 512 }),
      channelId: event.channelId,
      location: event.entityMetadata?.location || null,
      scheduledStartAt: event.scheduledStartTimestamp,
      scheduledEndAt: event.scheduledEndTimestamp,
      status: event.status,
      userCount: event.userCount || 0,
    }));
  } catch {
    return [];
  }
});

ipcMain.handle('leave-guild', async (_e, guildId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return { error: 'Guild not found' };
  try { await guild.leave(); return true; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('edit-guild', async (_e, guildId, data) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return null;
  try {
    const opts = {};
    if (data.name !== undefined) opts.name = data.name;
    if (data.description !== undefined) opts.description = data.description;
    if (data.verificationLevel !== undefined) opts.verificationLevel = data.verificationLevel;
    if (data.explicitContentFilter !== undefined) opts.explicitContentFilter = data.explicitContentFilter;
    if (data.defaultMessageNotifications !== undefined) opts.defaultMessageNotifications = data.defaultMessageNotifications;
    if (data.afkChannelId !== undefined) opts.afkChannel = data.afkChannelId;
    if (data.afkTimeout !== undefined) opts.afkTimeout = data.afkTimeout;
    if (data.systemChannelId !== undefined) opts.systemChannel = data.systemChannelId;
    await guild.edit(opts);
    return true;
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('set-guild-icon', async (_e, guildId) => {
  const result = await dialog.showOpenDialog(mainWindow, { properties: ['openFile'], filters: [{ name: 'Images', extensions: ['png','jpg','jpeg','gif','webp'] }] });
  if (result.canceled || !result.filePaths.length) return null;
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return null;
  const data = fs.readFileSync(result.filePaths[0]);
  const ext = path.extname(result.filePaths[0]).slice(1);
  await guild.setIcon(`data:image/${ext};base64,${data.toString('base64')}`);
  return { icon: guild.iconURL({ size: 256 }) };
});

// ── Channel Management ──
ipcMain.handle('get-channel-info', async (_e, channelId) => {
  const ch = client?.channels.cache.get(channelId);
  if (!ch) return null;
  return {
    id: ch.id, name: ch.name, type: ch.type,
    topic: ch.topic || '', nsfw: ch.nsfw || false,
    rateLimitPerUser: ch.rateLimitPerUser || 0,
    parentId: ch.parentId, position: ch.rawPosition,
    bitrate: ch.bitrate || null, userLimit: ch.userLimit || null,
    permissionOverwrites: ch.permissionOverwrites?.cache.map((p) => ({
      id: p.id, type: p.type,
      allow: p.allow.toArray(), deny: p.deny.toArray(),
    })) || [],
  };
});

ipcMain.handle('edit-channel', async (_e, channelId, data) => {
  const ch = client?.channels.cache.get(channelId);
  if (!ch) return null;
  try {
    const opts = {};
    if (data.name !== undefined) opts.name = data.name;
    if (data.topic !== undefined) opts.topic = data.topic;
    if (data.nsfw !== undefined) opts.nsfw = data.nsfw;
    if (data.rateLimitPerUser !== undefined) opts.rateLimitPerUser = data.rateLimitPerUser;
    if (data.parentId !== undefined) opts.parent = data.parentId || null;
    if (data.bitrate !== undefined) opts.bitrate = data.bitrate;
    if (data.userLimit !== undefined) opts.userLimit = data.userLimit;
    if (data.position !== undefined) opts.position = data.position;
    await ch.edit(opts);
    return true;
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('create-channel', async (_e, guildId, data) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return null;
  try {
    const ch = await guild.channels.create({
      name: data.name,
      type: data.type || ChannelType.GuildText,
      parent: data.parentId || null,
      topic: data.topic || null,
    });
    return { id: ch.id, name: ch.name, type: ch.type };
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('delete-channel', async (_e, channelId) => {
  const ch = client?.channels.cache.get(channelId);
  if (!ch) return false;
  try { await ch.delete(); return true; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('clone-channel', async (_e, channelId) => {
  const ch = client?.channels.cache.get(channelId);
  if (!ch) return null;
  try { const c = await ch.clone(); return { id: c.id, name: c.name }; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('set-channel-permissions', async (_e, channelId, targetId, type, allow, deny) => {
  const ch = client?.channels.cache.get(channelId);
  if (!ch) return false;
  try {
    await ch.permissionOverwrites.edit(targetId, {}, { type });
    const overwrite = {};
    if (allow) allow.forEach((p) => overwrite[p] = true);
    if (deny) deny.forEach((p) => overwrite[p] = false);
    await ch.permissionOverwrites.edit(targetId, overwrite);
    return true;
  } catch (e) { return { error: e.message }; }
});

// ── Role Management ──
ipcMain.handle('get-roles', async (_e, guildId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return [];
  return guild.roles.cache
    .sort((a, b) => b.position - a.position)
    .map((r) => ({
      id: r.id, name: r.name, color: r.hexColor,
      hoist: r.hoist, mentionable: r.mentionable,
      position: r.position, managed: r.managed,
      permissions: r.permissions.toArray(),
      memberCount: r.members.size,
      isEveryone: r.id === guild.id,
    }));
});

ipcMain.handle('create-role', async (_e, guildId, data) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return null;
  try {
    const r = await guild.roles.create({
      name: data.name || 'new role',
      color: data.color || null,
      hoist: data.hoist || false,
      mentionable: data.mentionable || false,
    });
    return { id: r.id, name: r.name, color: r.hexColor };
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('edit-role', async (_e, guildId, roleId, data) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return null;
  const role = guild.roles.cache.get(roleId);
  if (!role) return null;
  try {
    const opts = {};
    if (data.name !== undefined) opts.name = data.name;
    if (data.color !== undefined) opts.color = data.color;
    if (data.hoist !== undefined) opts.hoist = data.hoist;
    if (data.mentionable !== undefined) opts.mentionable = data.mentionable;
    if (data.permissions !== undefined) opts.permissions = data.permissions;
    await role.edit(opts);
    return true;
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('delete-role', async (_e, guildId, roleId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  const role = guild.roles.cache.get(roleId);
  if (!role) return false;
  try { await role.delete(); return true; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('add-role-to-member', async (_e, guildId, userId, roleId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try { const m = await guild.members.fetch(userId); await m.roles.add(roleId); return true; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('remove-role-from-member', async (_e, guildId, userId, roleId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try { const m = await guild.members.fetch(userId); await m.roles.remove(roleId); return true; } catch (e) { return { error: e.message }; }
});

// ── Member Management ──
ipcMain.handle('kick-member', async (_e, guildId, userId, reason) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try { const m = await guild.members.fetch(userId); await m.kick(reason || undefined); return true; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('ban-member', async (_e, guildId, userId, reason, days) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try {
    await guild.members.ban(userId, { reason: reason || undefined, deleteMessageSeconds: (days || 0) * 86400 });
    return true;
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('unban-member', async (_e, guildId, userId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try { await guild.members.unban(userId); return true; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('get-bans', async (_e, guildId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return [];
  try {
    const bans = await guild.bans.fetch();
    return bans.map((b) => ({
      userId: b.user.id, username: b.user.username,
      avatar: b.user.displayAvatarURL({ size: 64 }),
      reason: b.reason,
    }));
  } catch { return []; }
});

ipcMain.handle('timeout-member', async (_e, guildId, userId, duration) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try {
    const m = await guild.members.fetch(userId);
    await m.timeout(duration ? duration * 60000 : null);
    return true;
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('set-member-nickname', async (_e, guildId, userId, nick) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try { const m = await guild.members.fetch(userId); await m.setNickname(nick || null); return true; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('move-voice-member', async (_e, guildId, userId, channelId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try {
    const member = await guild.members.fetch(userId);
    await member.voice.setChannel(channelId || null);
    return true;
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('set-server-mute', async (_e, guildId, userId, muted) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try {
    const member = await guild.members.fetch(userId);
    await member.voice.setMute(Boolean(muted));
    return true;
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('set-server-deaf', async (_e, guildId, userId, deafened) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try {
    const member = await guild.members.fetch(userId);
    await member.voice.setDeaf(Boolean(deafened));
    return true;
  } catch (e) { return { error: e.message }; }
});

// ── Invites ──
ipcMain.handle('get-invites', async (_e, guildId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return [];
  try {
    const invites = await guild.invites.fetch();
    return invites.map((i) => ({
      code: i.code, url: i.url,
      channelName: i.channel?.name,
      inviter: i.inviter?.username,
      uses: i.uses, maxUses: i.maxUses,
      maxAge: i.maxAge, temporary: i.temporary,
      createdAt: i.createdTimestamp,
      expiresAt: i.expiresTimestamp,
    }));
  } catch { return []; }
});

ipcMain.handle('create-invite', async (_e, channelId, opts) => {
  const ch = client?.channels.cache.get(channelId);
  if (!ch) return null;
  try {
    const inv = await ch.createInvite({
      maxAge: opts?.maxAge ?? 86400,
      maxUses: opts?.maxUses ?? 0,
      temporary: opts?.temporary ?? false,
      unique: true,
    });
    return { code: inv.code, url: inv.url };
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('delete-invite', async (_e, code) => {
  try { const inv = await client.fetchInvite(code); await inv.delete(); return true; } catch (e) { return { error: e.message }; }
});

// ── Emoji Management ──
ipcMain.handle('get-emojis', async (_e, guildId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return [];
  return guild.emojis.cache.map((e) => ({
    id: e.id, name: e.name, animated: e.animated,
    url: e.imageURL({ size: 64 }),
    author: e.author?.username,
  }));
});

ipcMain.handle('create-emoji', async (_e, guildId, name) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return null;
  const result = await dialog.showOpenDialog(mainWindow, { properties: ['openFile'], filters: [{ name: 'Images', extensions: ['png','jpg','jpeg','gif','webp'] }] });
  if (result.canceled || !result.filePaths.length) return null;
  try {
    const data = fs.readFileSync(result.filePaths[0]);
    const ext = path.extname(result.filePaths[0]).slice(1);
    const emoji = await guild.emojis.create({ attachment: `data:image/${ext};base64,${data.toString('base64')}`, name: name || 'emoji' });
    return { id: emoji.id, name: emoji.name, url: emoji.imageURL({ size: 64 }) };
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('delete-emoji', async (_e, guildId, emojiId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try { const e = guild.emojis.cache.get(emojiId); if (e) await e.delete(); return true; } catch (e) { return { error: e.message }; }
});

ipcMain.handle('rename-emoji', async (_e, guildId, emojiId, newName) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return false;
  try { const e = guild.emojis.cache.get(emojiId); if (e) await e.edit({ name: newName }); return true; } catch (e) { return { error: e.message }; }
});

// ── Audit Log ──
ipcMain.handle('get-audit-log', async (_e, guildId, limit) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return [];
  try {
    const logs = await guild.fetchAuditLogs({ limit: limit || 50 });
    return logs.entries.map((e) => ({
      id: e.id, action: e.action, actionType: e.actionType,
      targetType: e.targetType,
      executor: e.executor ? { id: e.executor.id, username: e.executor.username, avatar: e.executor.displayAvatarURL({ size: 32 }) } : null,
      target: e.target ? { id: e.target.id, name: e.target.name || e.target.username || e.target.tag || String(e.target.id) } : null,
      reason: e.reason,
      changes: e.changes,
      createdAt: e.createdTimestamp,
    }));
  } catch { return []; }
});

// ── Webhooks ──
ipcMain.handle('get-webhooks', async (_e, guildId) => {
  const guild = client?.guilds.cache.get(guildId);
  if (!guild) return [];
  try {
    const hooks = await guild.fetchWebhooks();
    return hooks.map((w) => ({
      id: w.id, name: w.name, channelId: w.channelId,
      avatar: w.avatarURL({ size: 64 }),
      url: w.url, token: w.token,
      creator: w.owner?.username,
    }));
  } catch { return []; }
});

ipcMain.handle('delete-webhook', async (_e, webhookId) => {
  try {
    for (const guild of client.guilds.cache.values()) {
      const hooks = await guild.fetchWebhooks();
      const w = hooks.get(webhookId);
      if (w) { await w.delete(); return true; }
    }
    return false;
  } catch (e) { return { error: e.message }; }
});

// ── Pin messages ──
ipcMain.handle('pin-message', async (_e, channelId, messageId) => {
  const ch = client?.channels.cache.get(channelId);
  if (!ch) return false;
  const msg = await ch.messages.fetch(messageId);
  await msg.pin();
  return true;
});

ipcMain.handle('unpin-message', async (_e, channelId, messageId) => {
  const ch = client?.channels.cache.get(channelId);
  if (!ch) return false;
  const msg = await ch.messages.fetch(messageId);
  await msg.unpin();
  return true;
});

ipcMain.handle('get-pinned-messages', async (_e, channelId) => {
  const ch = client?.channels.cache.get(channelId);
  if (!ch) return [];
  const pinned = await ch.messages.fetchPinned();
  return pinned.map(serializeMessage);
});

// ── Bulk delete ──
ipcMain.handle('bulk-delete', async (_e, channelId, count) => {
  const ch = client?.channels.cache.get(channelId);
  if (!ch) return false;
  try { await ch.bulkDelete(count, true); return true; } catch (e) { return { error: e.message }; }
});

// ── Audio devices ──
ipcMain.handle('get-audio-devices', async () => {
  return mainWindow?.webContents.executeJavaScript(`
    navigator.mediaDevices.enumerateDevices().then(devices => {
      return devices.filter(d => d.kind === 'audioinput' || d.kind === 'audiooutput').map(d => ({
        deviceId: d.deviceId,
        kind: d.kind,
        label: d.label || (d.kind === 'audioinput' ? 'Microphone' : 'Speaker'),
        groupId: d.groupId,
      }));
    });
  `);
});

ipcMain.handle('set-audio-device', async (_e, kind, deviceId) => {
  if (!['audioinput', 'audiooutput'].includes(kind)) throw new Error('Invalid audio device type');
  const prefs = loadAudioPrefs();
  prefs[kind] = deviceId;
  saveAudioPrefs(prefs);
  mainWindow?.webContents.send('audio-device-changed', { kind, deviceId });
  return true;
});

ipcMain.handle('get-audio-prefs', async () => {
  return loadAudioPrefs();
});

// ── Threads ──
ipcMain.handle('get-threads', async (_e, channelId) => {
  const channel = client?.channels.cache.get(channelId);
  if (!channel || !channel.threads) return [];
  try {
    const fetched = await channel.threads.fetchActive();
    return fetched.threads.map((t) => ({
      id: t.id,
      name: t.name,
      messageCount: t.messageCount,
      memberCount: t.memberCount,
      archived: t.archived,
      parentId: t.parentId,
      createdTimestamp: t.createdTimestamp,
    }));
  } catch { return []; }
});

ipcMain.handle('get-thread-messages', async (_e, threadId, before) => {
  const channel = client?.channels.cache.get(threadId);
  if (!channel || !channel.isTextBased()) return [];
  const opts = { limit: 100 };
  if (before) opts.before = before;
  const messages = await channel.messages.fetch(opts);
  const result = [];
  for (const msg of messages.values()) {
    const s = serializeMessage(msg);
    await hydrateReferencedMessage(s, msg);
    result.push(s);
  }
  return result.reverse();
});

ipcMain.handle('send-thread-message', async (_e, threadId, content, replyToId) => {
  const channel = client?.channels.cache.get(threadId);
  if (!channel || !channel.isTextBased()) return null;
  const opts = { content };
  if (replyToId) {
    opts.reply = { messageReference: replyToId, failIfNotExists: false };
  }
  const msg = await channel.send(opts);
  const serialized = serializeMessage(msg);
  await hydrateReferencedMessage(serialized, msg);
  return serialized;
});

ipcMain.handle('create-thread', async (_e, channelId, name, messageId) => {
  const channel = client?.channels.cache.get(channelId);
  if (!channel) return null;
  try {
    let thread;
    if (messageId) {
      const message = await channel.messages.fetch(messageId);
      thread = await message.startThread({ name });
    } else {
      thread = await channel.threads.create({ name, type: ChannelType.PublicThread });
    }
    return { id: thread.id, name: thread.name };
  } catch (e) { return { error: e.message }; }
});

// ── Message Search ──
ipcMain.handle('search-messages', async (_e, guildId, query, channelId, authorId, limit) => {
  if (!client) return [];
  const maxResults = limit || 25;
  const queryLower = query.toLowerCase();
  const results = [];
  try {
    let channels;
    if (channelId) {
      const ch = client.channels.cache.get(channelId);
      channels = ch ? [ch] : [];
    } else {
      const guild = client.guilds.cache.get(guildId);
      if (!guild) return [];
      channels = guild.channels.cache.filter((c) => c.isTextBased()).values();
    }
    for (const ch of channels) {
      if (results.length >= maxResults) break;
      try {
        const messages = await ch.messages.fetch({ limit: 100 });
        for (const msg of messages.values()) {
          if (results.length >= maxResults) break;
          if (authorId && msg.author.id !== authorId) continue;
          if (msg.content.toLowerCase().includes(queryLower)) {
            results.push(serializeMessage(msg));
          }
        }
      } catch {}
    }
  } catch {}
  return results;
});

// ── Soundboard ──
ipcMain.handle('play-sound-to-voice', async (_e, guildId, soundPath, settings = {}) => {
  try {
    return await startSoundboardPlayback(guildId, soundPath, settings, 0);
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('pause-sound-to-voice', async (_e, guildId) => {
  const entry = activeSoundboards.get(guildId);
  if (!entry || entry.paused) return { success: true };
  entry.offsetMs = soundpadElapsedMs(entry);
  entry.paused = true;
  entry.intentionalStop = true;
  if (entry.idleHandler) {
    try { entry.player.off(AudioPlayerStatus.Idle, entry.idleHandler); } catch {}
  }
  try { entry.process?.kill?.('SIGKILL'); } catch {}
  try { entry.player.stop(true); } catch {}
  entry.process = null;
  entry.startedAt = Date.now();
  if (!voiceSelfMute && !voiceSelfDeaf) {
    startMicrophoneStream(guildId);
    entry.wasMicActive = true;
  }
  sendSoundpadState(guildId, 'paused', { path: entry.path, offsetMs: entry.offsetMs, durationMs: entry.durationMs || 0 });
  return { success: true, durationMs: entry.durationMs || 0, offsetMs: entry.offsetMs };
});

ipcMain.handle('resume-sound-to-voice', async (_e, guildId) => {
  const entry = activeSoundboards.get(guildId);
  if (!entry) return { error: 'No paused sound' };
  if (!entry.paused) return { success: true };
  return await startSoundboardPlayback(guildId, entry.path, entry.settings, entry.offsetMs, entry.wasMicActive);
});

ipcMain.handle('stop-sound-to-voice', async (_e, guildId) => {
  const entry = cleanupSoundboard(guildId, { resumeMic: true });
  sendSoundpadState(guildId, 'stopped', { path: entry?.path || null });
  return { success: true };
});

ipcMain.handle('seek-sound-to-voice', async (_e, guildId, deltaMs) => {
  const entry = activeSoundboards.get(guildId);
  if (!entry) return { error: 'No sound playing' };
  const nextOffset = Math.max(0, soundpadElapsedMs(entry) + Number(deltaMs || 0));
  if (entry.paused) {
    entry.offsetMs = nextOffset;
    sendSoundpadState(guildId, 'paused', { path: entry.path, offsetMs: entry.offsetMs, durationMs: entry.durationMs || 0 });
    return { success: true, durationMs: entry.durationMs || 0, offsetMs: entry.offsetMs };
  }
  return await startSoundboardPlayback(guildId, entry.path, entry.settings, nextOffset, entry.wasMicActive);
});

ipcMain.handle('seek-sound-to-voice-absolute', async (_e, guildId, offsetMs) => {
  const entry = activeSoundboards.get(guildId);
  if (!entry) return { error: 'No sound playing' };
  const durationMs = entry.durationMs || 0;
  const nextOffset = Math.max(0, durationMs ? Math.min(durationMs - 250, Number(offsetMs || 0)) : Number(offsetMs || 0));
  if (entry.paused) {
    entry.offsetMs = nextOffset;
    sendSoundpadState(guildId, 'paused', { path: entry.path, offsetMs: entry.offsetMs, durationMs });
    return { success: true, durationMs, offsetMs: entry.offsetMs };
  }
  return await startSoundboardPlayback(guildId, entry.path, entry.settings, nextOffset, entry.wasMicActive);
});

ipcMain.handle('update-sound-eq', async (_e, guildId, settings = {}) => {
  const entry = activeSoundboards.get(guildId);
  if (!entry) return { success: true };
  const nextSignature = buildSoundpadFilters(settings);
  const sameHeavyFilters = nextSignature === entry.filterSignature;
  entry.settings = settings;
  if (entry.paused) return { success: true };
  if (sameHeavyFilters) return { success: true, live: true };
  return await startSoundboardPlayback(guildId, entry.path, settings, soundpadElapsedMs(entry), entry.wasMicActive);
});

ipcMain.handle('select-sound-file', async () => {
  const result = await dialog.showOpenDialog(mainWindow, {
    properties: ['openFile'],
    filters: [{ name: 'Audio Files', extensions: ['mp3', 'wav', 'ogg', 'flac'] }],
  });
  if (result.canceled || !result.filePaths.length) return null;
  const filePath = result.filePaths[0];
  return { path: filePath, name: path.basename(filePath, path.extname(filePath)) };
});

ipcMain.handle('select-sound-files', async () => {
  const result = await dialog.showOpenDialog(mainWindow, {
    properties: ['openFile', 'multiSelections'],
    filters: [{ name: 'Audio Files', extensions: ['mp3', 'wav', 'ogg', 'flac', 'm4a', 'aac'] }],
  });
  if (result.canceled || !result.filePaths.length) return [];
  return result.filePaths.map((filePath) => ({
    path: filePath,
    name: path.basename(filePath, path.extname(filePath)),
  }));
});

ipcMain.handle('save-recording', async (_e, wavBuffer, name) => {
  try {
    const dir = path.join(app.getPath('userData'), 'recordings');
    if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
    const safe = String(name || 'recording').replace(/[<>:"/\\|?*]/g, '_').slice(0, 80);
    let filePath = path.join(dir, `${safe}.wav`);
    let n = 1;
    while (fs.existsSync(filePath)) { filePath = path.join(dir, `${safe}_${n++}.wav`); }
    fs.writeFileSync(filePath, Buffer.from(wavBuffer));
    return { path: filePath, name: safe };
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('get-recordings-path', async () => {
  return path.join(app.getPath('userData'), 'recordings');
});

ipcMain.handle('delete-recording', async (_e, filePath) => {
  try {
    if (fs.existsSync(filePath)) fs.unlinkSync(filePath);
    return true;
  } catch (e) { return { error: e.message }; }
});

// ── Keybinds (Global Shortcuts) ──
ipcMain.handle('register-keybind', async (_e, action, accelerator) => {
  try {
    globalShortcut.register(accelerator, () => {
      mainWindow?.webContents.send('keybind-triggered', action);
    });
    const keybinds = loadKeybinds();
    keybinds[action] = accelerator;
    saveKeybindsToFile(keybinds);
    return true;
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('unregister-keybind', async (_e, action) => {
  const keybinds = loadKeybinds();
  const accelerator = keybinds[action];
  if (accelerator) {
    try { globalShortcut.unregister(accelerator); } catch {}
    delete keybinds[action];
    saveKeybindsToFile(keybinds);
  }
  return true;
});

ipcMain.handle('get-keybinds', async () => {
  return loadKeybinds();
});

ipcMain.handle('save-keybinds', async (_e, keybinds) => {
  // Unregister all existing keybinds
  const old = loadKeybinds();
  for (const accelerator of Object.values(old)) {
    try { globalShortcut.unregister(accelerator); } catch {}
  }
  // Register all new keybinds
  for (const [action, accelerator] of Object.entries(keybinds)) {
    try {
      globalShortcut.register(accelerator, () => {
        mainWindow?.webContents.send('keybind-triggered', action);
      });
    } catch {}
  }
  saveKeybindsToFile(keybinds);
  return true;
});

// ── Notification Sounds ──
ipcMain.handle('play-notification-sound', async (_e, type) => {
  mainWindow?.webContents.send('notification-sound', { type, mentionsMe: type === 'mention' || type === 'call' });
  return true;
});

// ── Bot Activity ──
ipcMain.handle('set-bot-activity', async (_e, type, name) => {
  try {
    if (!client?.user) return { error: 'Not logged in' };
    client.user.setActivity(name, { type: ActivityType[type] || ActivityType.Playing });
    return true;
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('clear-bot-activity', async () => {
  try {
    if (!client?.user) return { error: 'Not logged in' };
    client.user.setPresence({ activities: [] });
    return true;
  } catch (e) { return { error: e.message }; }
});

// ── GIF Search (Tenor) ──
ipcMain.handle('search-gifs', async (_e, query) => {
  try {
    const url = `https://tenor.googleapis.com/v2/search?q=${encodeURIComponent(query)}&key=AIzaSyAyimkuYQYF_FXVALexPuGQctUWRURdCYQ&client_key=botcord&limit=20`;
    const res = await fetch(url);
    const data = await res.json();
    return (data.results || []).map((r) => ({
      id: r.id,
      url: r.media_formats?.tinygif?.url || '',
      preview: r.media_formats?.nanogif?.url || '',
    }));
  } catch (e) { return { error: e.message }; }
});

// ── File Upload (Drag & Drop) ──
ipcMain.handle('upload-file', async (_e, channelId, filePath, fileName) => {
  try {
    const channel = client?.channels.cache.get(channelId);
    if (!channel || !channel.isTextBased()) return { error: 'Channel not found' };
    const msg = await channel.send({ files: [{ attachment: filePath, name: fileName }] });
    return serializeMessage(msg);
  } catch (e) { return { error: e.message }; }
});

// ── TTS Message ──
ipcMain.handle('send-tts-message', async (_e, channelId, content) => {
  try {
    const channel = client?.channels.cache.get(channelId);
    if (!channel || !channel.isTextBased()) return { error: 'Channel not found' };
    const msg = await channel.send({ content, tts: true });
    return serializeMessage(msg);
  } catch (e) { return { error: e.message }; }
});

// ── System Tray ──
function createTray() {
  if (tray) return;
  const iconPath = fs.existsSync(path.join(__dirname, 'icon.ico'))
    ? path.join(__dirname, 'icon.ico')
    : path.join(__dirname, 'logo.webp');
  const icon = nativeImage.createFromPath(iconPath).resize({ width: 16, height: 16 });
  tray = new Tray(icon);
  tray.setToolTip('BotCord');
  const contextMenu = Menu.buildFromTemplate([
    { label: 'Open BotCord', click: () => { mainWindow?.show(); if (mainWindow?.isMinimized()) mainWindow.restore(); mainWindow?.focus(); } },
    { type: 'separator' },
    { label: 'Quit BotCord', click: () => { isQuitting = true; app.quit(); } },
  ]);
  tray.setContextMenu(contextMenu);
  tray.on('click', () => { mainWindow?.show(); if (mainWindow?.isMinimized()) mainWindow.restore(); mainWindow?.focus(); });
  tray.on('double-click', () => { mainWindow?.show(); if (mainWindow?.isMinimized()) mainWindow.restore(); mainWindow?.focus(); });
}

ipcMain.handle('enable-tray', async () => {
  try {
    createTray();
    return true;
  } catch (e) { return { error: e.message }; }
});

ipcMain.handle('disable-tray', async () => {
  try {
    if (tray) { tray.destroy(); tray = null; }
    return true;
  } catch (e) { return { error: e.message }; }
});

ipcMain.on('update-tray-badge', (_e, count) => {
  if (!tray) return;
  tray.setToolTip(count > 0 ? `BotCord (${count} unread)` : 'BotCord');
});
