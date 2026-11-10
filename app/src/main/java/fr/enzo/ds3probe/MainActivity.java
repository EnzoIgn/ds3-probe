package fr.enzo.ds3probe;

import android.app.Activity;
import android.content.BroadcastReceiver;
import android.content.ComponentName;
import android.content.ServiceConnection;
import android.content.ContentResolver;
import android.content.ContentValues;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.pm.ActivityInfo;
import android.content.pm.ApplicationInfo;
import android.content.pm.PackageInfo;
import android.content.pm.PackageManager;
import android.content.pm.ProviderInfo;
import android.content.pm.ServiceInfo;
import android.database.Cursor;
import android.graphics.Color;
import android.graphics.Typeface;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.os.Handler;
import android.os.IBinder;
import android.os.Parcel;
import android.os.Looper;
import android.provider.MediaStore;
import android.provider.Settings;
import android.view.ViewGroup;
import android.widget.Button;
import android.widget.LinearLayout;
import android.widget.ScrollView;
import android.widget.TextView;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.net.Inet4Address;
import java.net.InetAddress;
import java.net.NetworkInterface;
import java.net.ServerSocket;
import java.net.Socket;
import java.nio.charset.StandardCharsets;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Pattern;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

/**
 * DS3 Probe : diagnostic en lecture seule.
 * 1) Scanner : liste les applis constructeur / CANBUS, leurs composants exportés,
 *    les noms d'actions de broadcast et URI content:// trouvés dans leur code,
 *    les fournisseurs de contenu lisibles, les propriétés système et les ports série.
 * 2) Écouter : s'abonne à toutes les actions trouvées et journalise ce qui arrive
 *    (ouvrir une porte, passer la marche arrière, rouler...).
 * Le rapport est consultable depuis un autre appareil du même Wi-Fi : http://IP:8080
 * Rien n'est écrit dans le système, aucun port série n'est ouvert.
 */
public class MainActivity extends Activity {

    private static final int PORT = 8080;

    private static final String[] PKG_KEYWORDS = {
            "can", "car", "syu", "qf", "raise", "rzc", "hiworld", "xinpu", "fyt", "mcu",
            "vehicle", "obd", "jitu", "qianfeng", "bus", "zlink", "txz"
    };

    private static final String[] DATA_KEYWORDS = {
            "canbus", "can_", "carinfo", "car_info", "cardata", "car_data", "speed", "rpm",
            "door", "fuel", "mileage", "odometer", "odo", "trip", "reverse", "backcar",
            "radar", "temperature", "outtemp", "out_temp", "steer", "handbrake", "brake",
            "oil", "mcu", "battery", "voltage", "gear", "light", "seatbelt", "water", "coolant"
    };

    private static final String[] PROP_KEYWORDS = {
            "can", "car", "qf", "mcu", "raise", "syu", "fyt", "vehicle", "ro.product",
            "ro.build.display", "ro.board", "ro.hardware", "jitu", "bus"
    };

    private static final String[] KNOWN_ACTIONS = {
            "com.qf.vehicle.action.DOOR_WINDOW", "com.qf.vehicle.action.RADAR",
            "com.qf.vehicle.action.swa", "com.qf.action.headlight_state",
            "com.qf.action.BACKCAR_START", "com.qf.action.BACKCAR_STOP",
            "com.qf.action.ACC_ON", "com.qf.action.ACC_OFF",
            "com.qf.vehicle.action.ac_popup", "com.qf.vehicle.action.PANEL_KEY",
            "com.qf.vehicle.ACTION_DataTrace"
    };

    private static final Pattern ACTION_LIKE =
            Pattern.compile("^[A-Za-z][A-Za-z0-9_]*(\\.[A-Za-z0-9_]+){2,}$");

    private final Handler ui = new Handler(Looper.getMainLooper());
    private final StringBuilder report = new StringBuilder();
    private final Set<String> candidateActions = Collections.synchronizedSet(new TreeSet<>());
    private final Set<String> candidateUris = Collections.synchronizedSet(new TreeSet<>());
    private final Set<String> providerAuthorities = Collections.synchronizedSet(new TreeSet<>());
    private final List<ComponentName> qfServices = Collections.synchronizedList(new ArrayList<>());
    private volatile String canbusApk = null;

    private TextView out;
    private TextView info;
    private ScrollView scroll;
    private Button btnScan;
    private Button btnListen;

    private volatile boolean scanning = false;
    private BroadcastReceiver sniffer;
    private final Map<String, String> lastExtras = new HashMap<>();
    private final Map<String, Long> lastTime = new HashMap<>();
    private final Map<String, Integer> counts = new TreeMap<>();
    private ServerSocket server;

    // ------------------------------------------------------------------ UI

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);

        LinearLayout root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL);
        root.setBackgroundColor(Color.rgb(16, 20, 28));
        root.setPadding(16, 16, 16, 16);

        LinearLayout row = new LinearLayout(this);
        row.setOrientation(LinearLayout.HORIZONTAL);

        btnScan = makeButton("1. Scanner");
        btnListen = makeButton("2. Écouter");
        Button btnSave = makeButton("Enregistrer");
        Button btnClear = makeButton("Effacer");
        Button btnApk = makeButton("Copier APK");
        row.addView(btnScan, weight());
        row.addView(btnListen, weight());
        row.addView(btnSave, weight());
        row.addView(btnApk, weight());
        row.addView(btnClear, weight());

        info = new TextView(this);
        info.setTextColor(Color.rgb(140, 220, 255));
        info.setTextSize(15);
        info.setPadding(4, 12, 4, 12);

        scroll = new ScrollView(this);
        out = new TextView(this);
        out.setTextColor(Color.rgb(225, 230, 235));
        out.setTypeface(Typeface.MONOSPACE);
        out.setTextSize(12);
        out.setTextIsSelectable(true);
        scroll.addView(out);

        root.addView(row);
        root.addView(info);
        root.addView(scroll, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f));
        setContentView(root);

        btnScan.setOnClickListener(v -> startScan());
        btnListen.setOnClickListener(v -> toggleListen());
        btnSave.setOnClickListener(v -> saveReport());
        btnApk.setOnClickListener(v -> new Thread(this::copyCanbusApk, "apk").start());
        btnClear.setOnClickListener(v -> {
            synchronized (report) { report.setLength(0); }
            out.setText("");
            counts.clear();
        });

        startServer();
        log("DS3 Probe 1.1 — " + now());
        log("Étape 1 : appuie sur « 1. Scanner » (1 à 2 minutes).");
        log("Étape 2 : appuie sur « 2. Écouter », puis ouvre une portière, passe la marche");
        log("          arrière, allume les phares, démarre... puis réappuie pour arrêter.");
        log("Lecture seule : rien n'est modifié sur l'autoradio.");
        log("");
    }

    private Button makeButton(String text) {
        Button b = new Button(this);
        b.setText(text);
        b.setAllCaps(false);
        b.setTextSize(16);
        return b;
    }

    private LinearLayout.LayoutParams weight() {
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(0,
                ViewGroup.LayoutParams.WRAP_CONTENT, 1f);
        lp.setMargins(6, 0, 6, 0);
        return lp;
    }

    @Override
    protected void onDestroy() {
        stopListen();
        try { if (server != null) server.close(); } catch (Exception ignored) { }
        super.onDestroy();
    }

    private void log(String line) {
        synchronized (report) {
            report.append(line).append('\n');
        }
        ui.post(() -> {
            out.append(line + "\n");
            // Évite que l'affichage devienne énorme : le rapport complet reste en mémoire.
            if (out.length() > 200_000) {
                CharSequence t = out.getText();
                out.setText(t.subSequence(t.length() - 120_000, t.length()));
            }
            scroll.post(() -> scroll.fullScroll(ScrollView.FOCUS_DOWN));
        });
    }

    private void section(String title) {
        log("");
        log("==================== " + title + " ====================");
    }

    private static String now() {
        return new SimpleDateFormat("yyyy-MM-dd HH:mm:ss", Locale.FRANCE).format(new Date());
    }

    private static String time() {
        return new SimpleDateFormat("HH:mm:ss.SSS", Locale.FRANCE).format(new Date());
    }

    private static String cut(String s, int max) {
        if (s == null) return "null";
        return s.length() <= max ? s : s.substring(0, max) + "…";
    }

    private static boolean containsAny(String s, String[] kws) {
        String l = s.toLowerCase(Locale.ROOT);
        for (String k : kws) if (l.contains(k)) return true;
        return false;
    }

    // ------------------------------------------------------------------ SCAN

    private void startScan() {
        if (scanning) return;
        scanning = true;
        btnScan.setEnabled(false);
        new Thread(() -> {
            try {
                scanDevice();
                scanProps();
                scanPackages();
                scanProviders();
                probeServices();
                scanSettings();
                scanSerial();
                section("RÉSUMÉ");
                log("Actions candidates trouvées : " + candidateActions.size());
                log("URI content:// trouvées    : " + candidateUris.size());
                log("Scan terminé à " + now() + ". Tu peux lancer « 2. Écouter ».");
            } catch (Throwable t) {
                log("ERREUR scan : " + t);
            } finally {
                scanning = false;
                ui.post(() -> btnScan.setEnabled(true));
            }
        }, "scan").start();
    }

    private void scanDevice() {
        section("APPAREIL");
        log("Fabricant : " + Build.MANUFACTURER + " | Marque : " + Build.BRAND);
        log("Modèle    : " + Build.MODEL + " | Device : " + Build.DEVICE + " | Produit : " + Build.PRODUCT);
        log("Board     : " + Build.BOARD + " | Hardware : " + Build.HARDWARE);
        log("Android   : " + Build.VERSION.RELEASE + " (SDK " + Build.VERSION.SDK_INT + ")");
        log("Build     : " + Build.DISPLAY);
        log("Empreinte : " + Build.FINGERPRINT);
    }

    private void scanProps() {
        section("PROPRIÉTÉS SYSTÈME (filtrées)");
        try {
            Process p = Runtime.getRuntime().exec(new String[]{"getprop"});
            BufferedReader br = new BufferedReader(new InputStreamReader(p.getInputStream()));
            String line;
            int n = 0;
            while ((line = br.readLine()) != null) {
                if (containsAny(line, PROP_KEYWORDS)) {
                    log(cut(line, 200));
                    n++;
                }
            }
            log("(" + n + " lignes)");
        } catch (Exception e) {
            log("getprop impossible : " + e);
        }
    }

    private boolean isInteresting(String pkg, ApplicationInfo ai) {
        if (pkg.equals(getPackageName())) return false;
        String p = pkg.toLowerCase(Locale.ROOT);
        for (String k : PKG_KEYWORDS) if (p.contains(k)) return true;
        boolean system = (ai.flags & ApplicationInfo.FLAG_SYSTEM) != 0;
        return system
                && !p.startsWith("com.android.")
                && !p.startsWith("com.google.")
                && !p.startsWith("android")
                && !p.startsWith("com.sprd.")
                && !p.startsWith("com.unisoc.")
                && !p.startsWith("com.spreadtrum.");
    }

    @SuppressWarnings("deprecation")
    private void scanPackages() {
        PackageManager pm = getPackageManager();
        List<PackageInfo> all = pm.getInstalledPackages(0);
        List<PackageInfo> targets = new ArrayList<>();

        section("TOUTES LES APPLIS (" + all.size() + ")");
        Collections.sort(all, (a, b) -> a.packageName.compareTo(b.packageName));
        for (PackageInfo pi : all) {
            ApplicationInfo ai = pi.applicationInfo;
            if (ai == null) continue;
            boolean sys = (ai.flags & ApplicationInfo.FLAG_SYSTEM) != 0;
            boolean hit = isInteresting(pi.packageName, ai);
            log((hit ? "★ " : "  ") + (sys ? "[sys] " : "[usr] ") + pi.packageName
                    + "  v" + pi.versionName);
            if (hit) targets.add(pi);
        }

        section("APPLIS CONSTRUCTEUR / CANBUS (" + targets.size() + ")");
        int i = 0;
        for (PackageInfo base : targets) {
            i++;
            String pkg = base.packageName;
            final int idx = i;
            ui.post(() -> info.setText("Scan " + idx + "/" + targets.size() + " : " + pkg));
            log("");
            log("---- " + pkg + " ----");
            ApplicationInfo ai = base.applicationInfo;
            CharSequence label = "";
            try { label = pm.getApplicationLabel(ai); } catch (Exception ignored) { }
            log("Nom : " + label + " | APK : " + ai.sourceDir + " | uid " + ai.uid);
            if (ai.sharedLibraryFiles != null) log("Libs : " + Arrays.toString(ai.sharedLibraryFiles));

            if (pkg.equals("com.qf.vehicle")) canbusApk = ai.sourceDir;
            dumpComponents(pm, pkg);
            scanDex(ai);
        }
        ui.post(this::refreshInfo);
    }

    @SuppressWarnings("deprecation")
    private void dumpComponents(PackageManager pm, String pkg) {
        PackageInfo pi = null;
        try {
            pi = pm.getPackageInfo(pkg, PackageManager.GET_SERVICES
                    | PackageManager.GET_RECEIVERS | PackageManager.GET_PROVIDERS);
        } catch (Throwable t) {
            log("  (composants illisibles : " + t.getClass().getSimpleName() + ")");
        }
        if (pi == null) return;

        if (pi.services != null) for (ServiceInfo s : pi.services) {
            if (s.exported && pkg.startsWith("com.qf.")) qfServices.add(new ComponentName(pkg, s.name));
            log("  service  " + s.name + (s.exported ? " [exporté]" : "")
                    + (s.permission != null ? " perm=" + s.permission : ""));
        }
        if (pi.receivers != null) for (ActivityInfo r : pi.receivers) {
            log("  receiver " + r.name + (r.exported ? " [exporté]" : "")
                    + (r.permission != null ? " perm=" + r.permission : ""));
        }
        if (pi.providers != null) for (ProviderInfo p : pi.providers) {
            log("  provider " + p.name + " auth=" + p.authority + (p.exported ? " [exporté]" : "")
                    + (p.readPermission != null ? " read=" + p.readPermission : ""));
            if (p.exported && p.authority != null) {
                for (String a : p.authority.split(";")) providerAuthorities.add(a);
            }
        }
    }

    private void scanDex(ApplicationInfo ai) {
        List<String> files = new ArrayList<>();
        if (ai.sourceDir != null) files.add(ai.sourceDir);
        if (ai.splitSourceDirs != null) files.addAll(Arrays.asList(ai.splitSourceDirs));

        Set<String> actions = new TreeSet<>();
        Set<String> uris = new TreeSet<>();
        Set<String> keywords = new TreeSet<>();
        Set<String> classes = new TreeSet<>();
        int dexCount = 0;

        for (String f : files) {
            try (ZipFile zip = new ZipFile(f)) {
                Enumeration<? extends ZipEntry> en = zip.entries();
                while (en.hasMoreElements()) {
                    ZipEntry e = en.nextElement();
                    String n = e.getName();
                    if (!(n.startsWith("classes") && n.endsWith(".dex"))) continue;
                    dexCount++;
                    byte[] data = readAll(zip.getInputStream(e));
                    extractStrings(data, actions, uris, keywords, classes);
                }
            } catch (Throwable t) {
                log("  (lecture APK impossible : " + t.getClass().getSimpleName() + ")");
            }
        }
        if (dexCount == 0) {
            log("  (pas de code .dex lisible dans l'APK — code précompilé)");
            return;
        }

        log("  Actions candidates (" + actions.size() + ") :");
        int n = 0;
        for (String a : actions) {
            if (n++ >= 400) { log("    …"); break; }
            log("    " + a);
        }
        candidateActions.addAll(actions);

        if (!uris.isEmpty()) {
            log("  URI content:// (" + uris.size() + ") :");
            for (String u : uris) log("    " + u);
            candidateUris.addAll(uris);
        }

        if (!classes.isEmpty()) {
            log("  Interfaces / entités / AIDL (" + classes.size() + ") :");
            n = 0;
            for (String k : classes) {
                if (n++ >= 600) { log("    …"); break; }
                log("    " + k);
            }
        }

        if (!keywords.isEmpty()) {
            log("  Chaînes « données voiture » (" + keywords.size() + ") :");
            n = 0;
            for (String k : keywords) {
                if (n++ >= 250) { log("    …"); break; }
                log("    " + k);
            }
        }
    }

    private static byte[] readAll(InputStream in) throws Exception {
        try (InputStream is = in) {
            ByteArrayOutputStream bos = new ByteArrayOutputStream();
            byte[] buf = new byte[65536];
            int r;
            while ((r = is.read(buf)) > 0) bos.write(buf, 0, r);
            return bos.toByteArray();
        }
    }

    private void extractStrings(byte[] data, Set<String> actions, Set<String> uris,
                                Set<String> keywords, Set<String> classes) {
        StringBuilder cur = new StringBuilder();
        for (int i = 0; i <= data.length; i++) {
            int b = i < data.length ? (data[i] & 0xff) : 0;
            if (b >= 0x20 && b < 0x7f && cur.length() < 220) {
                cur.append((char) b);
                continue;
            }
            // Dans un .dex, chaque chaîne est précédée de sa longueur : on retire cet octet.
            if (b == 0 && cur.length() >= 33 && cur.charAt(0) == cur.length() - 1) cur.deleteCharAt(0);
            if (cur.length() >= 6) classify(cur.toString(), actions, uris, keywords, classes);
            cur.setLength(0);
        }
    }

    private void classify(String s, Set<String> actions, Set<String> uris, Set<String> keywords,
                          Set<String> classes) {
        if (s.startsWith("TRANSACTION_") || s.startsWith("DESCRIPTOR")) {
            classes.add(s);
            return;
        }
        if (s.startsWith("Lcom/") && s.endsWith(";") && !s.contains("$$")) {
            String simple = s.substring(s.lastIndexOf('/') + 1, s.length() - 1);
            String l = s.toLowerCase(Locale.ROOT);
            boolean aidlLike = simple.length() > 2 && simple.charAt(0) == 'I'
                    && Character.isUpperCase(simple.charAt(1));
            if (aidlLike || l.contains("/entity/") || l.contains("/aidl/") || l.contains("stub")
                    || l.contains("callback") || l.contains("listener") || l.contains("/bean/")
                    || l.contains("manager;") || l.contains("service;") || l.contains("canbus")
                    || l.contains("vehicle")) {
                if (l.startsWith("lcom/qf/") || l.startsWith("lcom/txz") || l.contains("can")
                        || l.contains("vehicle") || l.contains("car")) classes.add(s);
            }
            return;
        }
        if (s.startsWith("content://")) {
            if (!s.contains("%") && !s.contains(" ") && s.length() < 150) uris.add(s);
            return;
        }
        if (s.length() <= 120 && ACTION_LIKE.matcher(s).matches()) {
            String l = s.toLowerCase(Locale.ROOT);
            if (l.startsWith("android.") || l.startsWith("com.android.") || l.startsWith("com.google.")
                    || l.startsWith("java.") || l.startsWith("javax.") || l.startsWith("kotlin.")
                    || l.startsWith("androidx.") || l.startsWith("org.") || l.startsWith("dalvik.")) {
                return;
            }
            String last = s.substring(s.lastIndexOf('.') + 1);
            if (l.startsWith("com.qf.") && last.length() > 2 && last.charAt(0) == 'I'
                    && Character.isUpperCase(last.charAt(1))) {
                classes.add(s + "   (descripteur AIDL probable)");
            }
            boolean upperLast = last.length() >= 3 && last.equals(last.toUpperCase(Locale.ROOT))
                    && last.matches(".*[A-Z].*");
            if (l.contains("action") || upperLast) {
                actions.add(s);
                return;
            }
        }
        if (s.length() <= 80 && containsAny(s, DATA_KEYWORDS) && !s.contains(" ")) {
            keywords.add(s);
        }
    }

    private void scanProviders() {
        section("LECTURE DES FOURNISSEURS DE CONTENU");
        List<String> targets = new ArrayList<>();
        for (String a : providerAuthorities) targets.add("content://" + a);
        for (String u : candidateUris) if (!targets.contains(u)) targets.add(u);

        int n = 0;
        for (String u : targets) {
            String l = u.toLowerCase(Locale.ROOT);
            if (l.startsWith("content://com.android.") || l.startsWith("content://media")
                    || l.startsWith("content://com.google.") || l.startsWith("content://contacts")
                    || l.startsWith("content://sms") || l.startsWith("content://call_log")
                    || l.startsWith("content://telephony") || l.startsWith("content://settings")) {
                continue;
            }
            if (n++ >= 60) { log("(limite atteinte)"); break; }
            queryWithTimeout(Uri.parse(u));
        }
        if (n == 0) log("(aucun fournisseur exporté intéressant)");
    }

    private void queryWithTimeout(Uri uri) {
        final StringBuilder res = new StringBuilder();
        Thread t = new Thread(() -> {
            ContentResolver cr = getContentResolver();
            try (Cursor c = cr.query(uri, null, null, null, null)) {
                if (c == null) { res.append("null"); return; }
                res.append(c.getCount()).append(" lignes, colonnes=")
                        .append(Arrays.toString(c.getColumnNames()));
                int rows = 0;
                while (c.moveToNext() && rows < 8) {
                    StringBuilder r = new StringBuilder("\n      ");
                    for (int i = 0; i < c.getColumnCount(); i++) {
                        String v;
                        try {
                            int type = c.getType(i);
                            v = type == Cursor.FIELD_TYPE_BLOB ? "<blob>" : c.getString(i);
                        } catch (Exception e) { v = "?"; }
                        r.append(c.getColumnName(i)).append('=').append(cut(v, 60)).append("  ");
                    }
                    res.append(r);
                    rows++;
                }
            } catch (Throwable e) {
                res.append("refusé/erreur : ").append(e.getClass().getSimpleName())
                        .append(" ").append(cut(String.valueOf(e.getMessage()), 120));
            }
        });
        t.setDaemon(true);
        t.start();
        try { t.join(3000); } catch (InterruptedException ignored) { }
        log("  " + uri + " → " + (t.isAlive() ? "pas de réponse (timeout)" : res));
    }

    private void scanSettings() {
        section("PARAMÈTRES SYSTÈME (clés voiture)");
        dumpSettingsTable(Settings.System.CONTENT_URI, "system");
        dumpSettingsTable(Settings.Global.CONTENT_URI, "global");
    }

    private void dumpSettingsTable(Uri uri, String name) {
        try (Cursor c = getContentResolver().query(uri, new String[]{"name", "value"},
                null, null, null)) {
            if (c == null) { log(name + " : null"); return; }
            int total = 0, shown = 0;
            while (c.moveToNext()) {
                total++;
                String k = c.getString(0);
                String v = c.getString(1);
                if (k != null && (containsAny(k, PKG_KEYWORDS) || containsAny(k, DATA_KEYWORDS))) {
                    log("  " + name + "." + k + " = " + cut(v, 100));
                    shown++;
                }
            }
            log("  (" + name + " : " + total + " clés, " + shown + " affichées)");
        } catch (Throwable t) {
            log("  " + name + " illisible : " + t.getClass().getSimpleName());
        }
    }

    private void scanSerial() {
        section("PORTS SÉRIE / PÉRIPHÉRIQUES");
        File dev = new File("/dev");
        String[] names = dev.list();
        if (names == null) {
            log("/dev non listable");
        } else {
            Arrays.sort(names);
            int n = 0;
            for (String nm : names) {
                String l = nm.toLowerCase(Locale.ROOT);
                if (l.startsWith("tty") && !l.matches("tty\\d*") || l.contains("can")
                        || l.contains("mcu") || l.contains("car") || l.contains("serial")) {
                    File f = new File(dev, nm);
                    log("  /dev/" + nm + "  lecture=" + f.canRead() + " écriture=" + f.canWrite());
                    n++;
                }
            }
            log("  (" + n + " entrées)");
        }
        File tty = new File("/sys/class/tty");
        String[] t = tty.list();
        if (t != null) {
            Arrays.sort(t);
            StringBuilder sb = new StringBuilder("  /sys/class/tty : ");
            for (String s : t) if (!s.matches("tty\\d*")) sb.append(s).append(' ');
            log(sb.toString());
        }
    }

    private void probeServices() {
        section("SERVICES QF (descripteurs AIDL)");
        List<ComponentName> list;
        synchronized (qfServices) { list = new ArrayList<>(qfServices); }
        if (list.isEmpty()) { log("(aucun service QF exporté)"); return; }
        for (ComponentName cn : list) {
            final Object lock = new Object();
            final String[] result = {null};
            ServiceConnection conn = new ServiceConnection() {
                @Override
                public void onServiceConnected(ComponentName name, IBinder service) {
                    String d;
                    try { d = service == null ? "binder null" : service.getInterfaceDescriptor(); }
                    catch (Throwable t) { d = "erreur " + t.getClass().getSimpleName(); }
                    synchronized (lock) { result[0] = "connecté, descripteur = " + d; lock.notifyAll(); }
                }
                @Override
                public void onServiceDisconnected(ComponentName name) { }
            };
            boolean ok;
            try {
                Intent i = new Intent();
                i.setComponent(cn);
                // flag 0 : on ne démarre rien, on se connecte seulement si le service tourne déjà.
                ok = bindService(i, conn, 0);
            } catch (Throwable t) {
                log("  " + cn.flattenToShortString() + " → refusé : " + t.getClass().getSimpleName()
                        + " " + cut(String.valueOf(t.getMessage()), 100));
                continue;
            }
            if (!ok) {
                log("  " + cn.flattenToShortString() + " → bindService=false");
                continue;
            }
            synchronized (lock) {
                try { if (result[0] == null) lock.wait(4000); } catch (InterruptedException ignored) { }
            }
            log("  " + cn.flattenToShortString() + " → "
                    + (result[0] != null ? result[0] : "pas de réponse (service non démarré ?)"));
            try { unbindService(conn); } catch (Throwable ignored) { }
        }
    }

    private void copyCanbusApk() {
        String src = canbusApk;
        if (src == null) src = "/system/priv-app/QF_Canbus/QF_Canbus.apk";
        File f = new File(src);
        if (!f.canRead()) { log("APK illisible : " + src); return; }
        try {
            ContentValues cv = new ContentValues();
            cv.put(MediaStore.MediaColumns.DISPLAY_NAME, "QF_Canbus.apk.bin");
            cv.put(MediaStore.MediaColumns.MIME_TYPE, "application/octet-stream");
            cv.put(MediaStore.MediaColumns.RELATIVE_PATH, "Download");
            Uri u = getContentResolver().insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, cv);
            if (u == null) throw new IllegalStateException("insert null");
            try (InputStream in = new FileInputStream(f);
                 OutputStream os = getContentResolver().openOutputStream(u)) {
                if (os == null) throw new IllegalStateException("flux null");
                byte[] buf = new byte[65536];
                int r;
                while ((r = in.read(buf)) > 0) os.write(buf, 0, r);
            }
            log("APK canbus copié : Download/QF_Canbus.apk.bin (" + (f.length() / 1024) + " Ko)");
            log("Ou depuis l'iPhone : même adresse, mais finissant par /canbus.apk");
        } catch (Throwable t) {
            log("Copie APK impossible : " + t);
        }
    }

    // ------------------------------------------------------------------ ÉCOUTE

    private void toggleListen() {
        if (sniffer != null) {
            stopListen();
            return;
        }
        if (candidateActions.isEmpty()) {
            log("(Scan non lancé : écoute des actions connues seulement.)");
        }
        IntentFilter filter = new IntentFilter();
        int n = 0;
        for (String a : KNOWN_ACTIONS) { filter.addAction(a); n++; }
        synchronized (candidateActions) {
            for (String a : candidateActions) {
                if (!filter.hasAction(a)) filter.addAction(a);
                if (++n >= 3000) break;
            }
        }
        sniffer = new BroadcastReceiver() {
            @Override
            public void onReceive(Context context, Intent intent) {
                onSniffed(intent);
            }
        };
        try {
            if (Build.VERSION.SDK_INT >= 33) {
                registerReceiver(sniffer, filter, Context.RECEIVER_EXPORTED);
            } else {
                registerReceiver(sniffer, filter);
            }
            section("ÉCOUTE DÉMARRÉE (" + n + " actions) — " + now());
            log("Ouvre/ferme une portière, passe la marche arrière, allume les phares,");
            log("tourne le volant, démarre le moteur… puis appuie sur « Arrêter ».");
            btnListen.setText("Arrêter");
        } catch (Throwable t) {
            log("Impossible d'écouter : " + t);
            sniffer = null;
        }
    }

    private void stopListen() {
        if (sniffer == null) return;
        try { unregisterReceiver(sniffer); } catch (Exception ignored) { }
        sniffer = null;
        section("ÉCOUTE ARRÊTÉE — " + now());
        if (counts.isEmpty()) {
            log("Aucun message reçu.");
        } else {
            log("Messages reçus par action :");
            for (Map.Entry<String, Integer> e : counts.entrySet()) {
                log("  " + e.getValue() + " × " + e.getKey());
            }
        }
        ui.post(() -> btnListen.setText("2. Écouter"));
    }

    private void onSniffed(Intent intent) {
        String action = String.valueOf(intent.getAction());
        String raw = rawIntent(intent);
        Integer c = counts.get(action);
        counts.put(action, c == null ? 1 : c + 1);

        String extras;
        try {
            extras = describeExtras(intent.getExtras());
        } catch (Throwable t) {
            extras = "{illisible:" + t.getClass().getSimpleName() + "}";
        }
        if (extras.contains("illisible")) extras = extras + "  RAW=" + raw;
        long t = System.currentTimeMillis();
        String prev = lastExtras.get(action);
        Long prevT = lastTime.get(action);
        // Évite le spam : on journalise si le contenu change, ou toutes les 5 s.
        if (extras.equals(prev) && prevT != null && t - prevT < 5000) return;
        lastExtras.put(action, extras);
        lastTime.put(action, t);
        log(time() + "  " + action + "  " + extras);
    }

    /** Copie brute de l'intent (marche même si les objets ne sont pas connus de l'appli). */
    private static String rawIntent(Intent intent) {
        Parcel p = Parcel.obtain();
        try {
            intent.writeToParcel(p, 0);
            byte[] a = p.marshall();
            StringBuilder hex = new StringBuilder("hex[");
            StringBuilder asc = new StringBuilder(" ascii[");
            for (int i = 0; i < a.length && i < 768; i++) {
                hex.append(String.format("%02X", a[i]));
                if (i % 4 == 3) hex.append(' ');
                int c = a[i] & 0xff;
                asc.append(c >= 0x20 && c < 0x7f ? (char) c : '.');
            }
            return hex.append("] len=").append(a.length).append(asc).append(']').toString();
        } catch (Throwable t) {
            return "raw illisible:" + t.getClass().getSimpleName();
        } finally {
            p.recycle();
        }
    }

    @SuppressWarnings("deprecation")
    private static String describeExtras(Bundle b) {
        if (b == null) return "{}";
        StringBuilder sb = new StringBuilder("{");
        try {
            List<String> keys = new ArrayList<>(b.keySet());
            Collections.sort(keys);
            for (String k : keys) {
                Object v = b.get(k);
                sb.append(k).append('=').append(cut(valueToString(v), 300)).append("; ");
            }
        } catch (Throwable t) {
            sb.append("illisible:").append(t.getClass().getSimpleName());
        }
        return sb.append('}').toString();
    }

    private static String valueToString(Object v) {
        if (v == null) return "null";
        if (v instanceof byte[]) {
            byte[] a = (byte[]) v;
            StringBuilder sb = new StringBuilder("hex[");
            for (int i = 0; i < a.length && i < 96; i++) sb.append(String.format("%02X ", a[i]));
            return sb.append(']').toString();
        }
        if (v instanceof int[]) return Arrays.toString((int[]) v);
        if (v instanceof long[]) return Arrays.toString((long[]) v);
        if (v instanceof float[]) return Arrays.toString((float[]) v);
        if (v instanceof String[]) return Arrays.toString((String[]) v);
        if (v instanceof Bundle) return describeExtras((Bundle) v);
        return v.getClass().getSimpleName() + ":" + v;
    }

    // ------------------------------------------------------------------ PARTAGE

    private String reportText() {
        synchronized (report) {
            return report.toString();
        }
    }

    private void saveReport() {
        String name = "ds3probe_" + new SimpleDateFormat("yyyyMMdd_HHmmss", Locale.FRANCE)
                .format(new Date()) + ".txt";
        byte[] data = reportText().getBytes(StandardCharsets.UTF_8);
        try {
            if (Build.VERSION.SDK_INT >= 29) {
                ContentValues cv = new ContentValues();
                cv.put(MediaStore.MediaColumns.DISPLAY_NAME, name);
                cv.put(MediaStore.MediaColumns.MIME_TYPE, "text/plain");
                cv.put(MediaStore.MediaColumns.RELATIVE_PATH, "Download");
                Uri u = getContentResolver().insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, cv);
                if (u == null) throw new IllegalStateException("insert null");
                try (OutputStream os = getContentResolver().openOutputStream(u)) {
                    if (os == null) throw new IllegalStateException("flux null");
                    os.write(data);
                }
                log("Rapport enregistré : Download/" + name);
            } else {
                File f = new File(getExternalFilesDir(null), name);
                try (OutputStream os = new java.io.FileOutputStream(f)) { os.write(data); }
                log("Rapport enregistré : " + f.getAbsolutePath());
            }
        } catch (Throwable t) {
            log("Enregistrement impossible : " + t);
        }
    }

    private void startServer() {
        Thread th = new Thread(() -> {
            try {
                server = new ServerSocket(PORT);
                while (!server.isClosed()) {
                    Socket s = server.accept();
                    handleClient(s);
                }
            } catch (Throwable t) {
                if (server == null || !server.isClosed()) log("Serveur web arrêté : " + t);
            }
        }, "http");
        th.setDaemon(true);
        th.start();
        ui.post(this::refreshInfo);
    }

    private void handleClient(Socket s) {
        try (Socket sock = s) {
            sock.setSoTimeout(5000);
            BufferedReader br = new BufferedReader(new InputStreamReader(sock.getInputStream()));
            String req = br.readLine();
            String path = "/";
            if (req != null) {
                String[] parts = req.split(" ");
                if (parts.length > 1) path = parts[1];
            }
            String line;
            while ((line = br.readLine()) != null && !line.isEmpty()) { /* en-têtes ignorés */ }

            OutputStream os = sock.getOutputStream();
            if (path.startsWith("/canbus.apk")) {
                String src = canbusApk != null ? canbusApk : "/system/priv-app/QF_Canbus/QF_Canbus.apk";
                File f = new File(src);
                String hd = "HTTP/1.1 200 OK\r\nContent-Type: application/octet-stream\r\n"
                        + "Content-Disposition: attachment; filename=\"QF_Canbus.apk.bin\"\r\n"
                        + "Content-Length: " + f.length() + "\r\nConnection: close\r\n\r\n";
                os.write(hd.getBytes(StandardCharsets.US_ASCII));
                try (InputStream in = new FileInputStream(f)) {
                    byte[] buf = new byte[65536];
                    int r;
                    while ((r = in.read(buf)) > 0) os.write(buf, 0, r);
                }
                os.flush();
                return;
            }
            byte[] body = reportText().getBytes(StandardCharsets.UTF_8);
            StringBuilder h = new StringBuilder();
            h.append("HTTP/1.1 200 OK\r\n");
            h.append("Content-Type: text/plain; charset=utf-8\r\n");
            if (path.contains("download") || path.endsWith(".txt")) {
                h.append("Content-Disposition: attachment; filename=\"ds3probe.txt\"\r\n");
            }
            h.append("Cache-Control: no-store\r\n");
            h.append("Content-Length: ").append(body.length).append("\r\n");
            h.append("Connection: close\r\n\r\n");
            os.write(h.toString().getBytes(StandardCharsets.US_ASCII));
            os.write(body);
            os.flush();
        } catch (Throwable ignored) {
        }
    }

    private void refreshInfo() {
        List<String> ips = new ArrayList<>();
        try {
            Enumeration<NetworkInterface> ifs = NetworkInterface.getNetworkInterfaces();
            while (ifs != null && ifs.hasMoreElements()) {
                NetworkInterface ni = ifs.nextElement();
                Enumeration<InetAddress> as = ni.getInetAddresses();
                while (as.hasMoreElements()) {
                    InetAddress a = as.nextElement();
                    if (a instanceof Inet4Address && !a.isLoopbackAddress()) {
                        ips.add("http://" + a.getHostAddress() + ":" + PORT + "/ds3probe.txt");
                    }
                }
            }
        } catch (Exception ignored) { }
        if (ips.isEmpty()) {
            info.setText("Rapport : connecte l'autoradio au Wi-Fi (partage iPhone) pour le récupérer.");
        } else {
            info.setText("Rapport depuis l'iPhone (même Wi-Fi) : " + String.join("  ou  ", ips));
        }
    }
}
