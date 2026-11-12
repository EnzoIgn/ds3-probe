package fr.enzo.ds3probe;

import android.content.Context;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Proxy;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

/**
 * Écoute brute des trames du boîtier CANBUS Raise, au même endroit que l'appli d'origine :
 * le service système « mcu_service » (android.qf.mcu.McuManager).
 *
 * Format Raise (protocole PSA) : 2E type len data[len] checksum
 *   checksum = (type + len + somme(data)) XOR 0xFF
 *   0x33 = ordinateur de bord page 0 : conso instantanée, AUTONOMIE, distance destination
 *   0x34 / 0x35 = trajets 1 et 2 : conso moyenne, vitesse moyenne, distance
 *   0x36 = température extérieure
 */
final class McuTap {

    interface Sink {
        void log(String line);
        void live(String line);
    }

    private static final String MGR_CLASS = "android.qf.mcu.McuManager";
    private static final String LISTENER_CLASS = "android.qf.mcu.McuListener";

    private final Context ctx;
    private final Sink sink;
    private Object manager;
    private Object listener;
    private Class<?> listenerClass;
    private volatile boolean running;

    private final ByteArrayOutputStream pending = new ByteArrayOutputStream();
    private final Map<String, Integer> counts = new TreeMap<>();
    private final Map<Integer, String> lastFrame = new HashMap<>();
    private final Map<Integer, Long> lastFrameTime = new HashMap<>();
    private final Map<String, String> lastRaw = new HashMap<>();

    // Dernières valeurs décodées, affichées en direct
    private String vAutonomie = "?", vConsoInst = "?", vConsoMoy1 = "?", vVitMoy1 = "?",
            vTrajet1 = "?", vConsoMoy2 = "?", vVitMoy2 = "?", vTrajet2 = "?", vTemp = "?", vDest = "?";

    McuTap(Context ctx, Sink sink) {
        this.ctx = ctx;
        this.sink = sink;
    }

    boolean isRunning() { return running; }

    // ------------------------------------------------------------------ inspection

    /** Décrit McuManager / McuListener sans rien brancher. */
    void inspect() {
        sink.log("BOOTCLASSPATH=" + System.getenv("BOOTCLASSPATH"));
        sink.log("SYSTEMSERVERCLASSPATH=" + System.getenv("SYSTEMSERVERCLASSPATH"));
        Object m = null;
        try {
            m = ctx.getSystemService("mcu_service");
            sink.log("getSystemService(\"mcu_service\") = " + (m == null ? "null" : m.getClass().getName()));
        } catch (Throwable t) {
            sink.log("getSystemService(\"mcu_service\") : " + t);
        }
        for (String cn : new String[]{MGR_CLASS, LISTENER_CLASS, "android.qf.mcu.IMcuService",
                "android.qf.mcu.IMcuListener", "android.qf.mcu.IMcuService$Stub"}) {
            try {
                Class<?> c = Class.forName(cn);
                sink.log("");
                sink.log("Classe " + cn + (c.isInterface() ? " (interface)" : "")
                        + " extends " + (c.getSuperclass() == null ? "-" : c.getSuperclass().getName()));
                for (Class<?> i : c.getInterfaces()) sink.log("  implements " + i.getName());
                for (java.lang.reflect.Field f : c.getDeclaredFields()) {
                    String val = "";
                    if (Modifier.isStatic(f.getModifiers())) {
                        try { f.setAccessible(true); val = " = " + f.get(null); } catch (Throwable ignored) { }
                    }
                    sink.log("  champ " + Modifier.toString(f.getModifiers()) + " "
                            + f.getType().getSimpleName() + " " + f.getName() + val);
                }
                for (Method me : c.getDeclaredMethods()) {
                    sink.log("  " + Modifier.toString(me.getModifiers()) + " "
                            + me.getReturnType().getSimpleName() + " " + me.getName() + sig(me));
                }
            } catch (Throwable t) {
                sink.log("Classe " + cn + " : " + t);
            }
        }
        if (m != null) {
            for (String getter : new String[]{"RPC_GetMcuVer", "RPC_GetChannel"}) {
                try {
                    Method me = m.getClass().getMethod(getter);
                    Object r = me.invoke(m);
                    sink.log(getter + "() = " + (r instanceof byte[] ? hex((byte[]) r) + "  « "
                            + ascii((byte[]) r) + " »" : String.valueOf(r)));
                } catch (Throwable t) {
                    sink.log(getter + "() : " + root(t));
                }
            }
        }
        String jar = findMcuJar();
        sink.log("Fichier qui contient McuManager : " + (jar == null ? "introuvable" : jar));
    }

    /** Cherche le .jar du framework qui contient android.qf.mcu.McuManager (pour /mcu.jar). */
    static String findMcuJar() {
        List<String> candidates = new ArrayList<>();
        for (String env : new String[]{"BOOTCLASSPATH", "SYSTEMSERVERCLASSPATH"}) {
            String v = System.getenv(env);
            if (v != null) for (String p : v.split(":")) if (!p.isEmpty()) candidates.add(p);
        }
        File[] fw = new File("/system/framework").listFiles();
        if (fw != null) for (File f : fw) if (f.getName().endsWith(".jar")) candidates.add(f.getPath());
        byte[] needle = "Landroid/qf/mcu/McuManager;".getBytes();
        for (String p : candidates) {
            File f = new File(p);
            if (!f.canRead()) continue;
            try (ZipFile z = new ZipFile(f)) {
                Enumeration<? extends ZipEntry> en = z.entries();
                while (en.hasMoreElements()) {
                    ZipEntry e = en.nextElement();
                    if (!e.getName().endsWith(".dex")) continue;
                    byte[] data = readAll(z.getInputStream(e));
                    if (indexOf(data, needle) >= 0) return p;
                }
            } catch (Throwable ignored) { }
        }
        return null;
    }

    // ------------------------------------------------------------------ écoute

    boolean start() {
        try {
            manager = ctx.getSystemService("mcu_service");
            if (manager == null) {
                sink.log("mcu_service introuvable : impossible de brancher l'écoute brute.");
                return false;
            }
            listenerClass = Class.forName(LISTENER_CLASS);
            if (!listenerClass.isInterface()) {
                sink.log("McuListener n'est pas une interface (" + listenerClass.getSuperclass()
                        + ") : branchement impossible par cette méthode.");
                return false;
            }
            InvocationHandler h = new InvocationHandler() {
                @Override
                public Object invoke(Object proxy, Method method, Object[] args) {
                    String n = method.getName();
                    if (n.equals("hashCode")) return System.identityHashCode(proxy);
                    if (n.equals("equals")) return args != null && args.length == 1 && proxy == args[0];
                    if (n.equals("toString")) return "DS3ProbeMcuListener";
                    try {
                        if (args != null && args.length == 1 && args[0] instanceof byte[]) {
                            onRaw(n, (byte[]) args[0]);
                        } else {
                            countRaw(n + "(" + (args == null ? 0 : args.length) + " args)");
                        }
                    } catch (Throwable t) {
                        sink.log("Erreur traitement trame : " + t);
                    }
                    Class<?> rt = method.getReturnType();
                    if (rt == boolean.class) return false;
                    if (rt == int.class || rt == byte.class || rt == short.class) return 0;
                    if (rt == long.class) return 0L;
                    return null;
                }
            };
            listener = Proxy.newProxyInstance(listenerClass.getClassLoader(),
                    new Class<?>[]{listenerClass}, h);
            Method reg = manager.getClass().getMethod("RPC_RequestMcuInfoChangedListener", listenerClass);
            reg.invoke(manager, listener);
            running = true;
            sink.log("Écoute brute branchée sur mcu_service (" + manager.getClass().getName() + ").");
            return true;
        } catch (Throwable t) {
            sink.log("Branchement mcu_service refusé : " + root(t));
            return false;
        }
    }

    void stop() {
        if (!running) return;
        running = false;
        boolean removed = false;
        if (manager != null && listener != null) {
            for (Method m : manager.getClass().getMethods()) {
                String n = m.getName().toLowerCase();
                Class<?>[] p = m.getParameterTypes();
                if (p.length == 1 && p[0] == listenerClass
                        && (n.contains("unregister") || n.contains("remove") || n.contains("release")
                        || n.contains("cancel") || n.contains("unrequest"))) {
                    try {
                        m.invoke(manager, listener);
                        sink.log("Écoute retirée avec " + m.getName() + "().");
                        removed = true;
                        break;
                    } catch (Throwable t) {
                        sink.log(m.getName() + "() : " + root(t));
                    }
                }
            }
        }
        if (!removed) sink.log("Pas de méthode de retrait trouvée : l'écoute s'arrêtera à la fermeture de l'appli.");
        sink.log("Trames reçues :");
        synchronized (this) {
            for (Map.Entry<String, Integer> e : counts.entrySet()) {
                sink.log("  " + e.getValue() + " × " + e.getKey());
            }
        }
        sink.log("Dernières valeurs ordinateur de bord : " + summary());
    }

    // ------------------------------------------------------------------ trames

    private synchronized void countRaw(String key) {
        Integer c = counts.get(key);
        counts.put(key, c == null ? 1 : c + 1);
    }

    private synchronized void onRaw(String method, byte[] raw) {
        if (raw == null || raw.length == 0) { countRaw("vide"); return; }
        int head = raw[0] & 0xff;
        String kind = head == 0x41 ? "CAN(41)" : head == 0x19 ? "MCU(19)" : String.format("autre(%02X)", head);
        countRaw("brut " + kind);
        // Journalise un échantillon de chaque sorte de bloc brut (dédoublonné)
        String key = kind + (raw.length > 1 ? String.format("/%02X", raw[1] & 0xff) : "");
        String hx = hex(raw);
        if (!hx.equals(lastRaw.get(key)) && lastRaw.size() < 400) {
            lastRaw.put(key, hx);
            sink.log(MainActivity.time() + "  [MCU " + method + "] " + hx);
        }
        if (head != 0x41) return;
        pending.write(raw, 1, raw.length - 1);
        drain();
    }

    private void drain() {
        byte[] b = pending.toByteArray();
        int i = 0;
        while (i < b.length) {
            if ((b[i] & 0xff) != 0x2E) { i++; continue; }
            if (i + 3 > b.length) break;
            int len = b[i + 2] & 0xff;
            if (len > 100) { i++; continue; }
            int total = len + 4;
            if (i + total > b.length) break;
            int sum = 0;
            for (int k = i + 1; k < i + total - 1; k++) sum += b[k] & 0xff;
            int cs = (sum & 0xff) ^ 0xff;
            if (cs != (b[i + total - 1] & 0xff)) { i++; continue; }
            byte[] f = new byte[total];
            System.arraycopy(b, i, f, 0, total);
            onFrame(f);
            i += total;
        }
        pending.reset();
        if (i < b.length) {
            int keep = Math.min(b.length - i, 512);
            pending.write(b, b.length - keep, keep);
        }
    }

    private void onFrame(byte[] f) {
        int type = f[1] & 0xff;
        countRaw(String.format("trame Raise 0x%02X (%s)", type, typeName(type)));
        String hx = hex(f);
        long t = System.currentTimeMillis();
        String prev = lastFrame.get(type);
        Long pt = lastFrameTime.get(type);
        String dec = decode(f);
        if (hx.equals(prev) && pt != null && t - pt < 5000) return;
        lastFrame.put(type, hx);
        lastFrameTime.put(type, t);
        sink.log(MainActivity.time() + "  [Raise 0x" + String.format("%02X", type) + " "
                + typeName(type) + "] " + hx + (dec == null ? "" : "\n      → " + dec));
        if (dec != null && type >= 0x33 && type <= 0x36) sink.live(summary());
    }

    private static int u16(byte[] f, int i) {
        return ((f[i] & 0xff) << 8) | (f[i + 1] & 0xff);
    }

    private static String x10(int v) { return (v / 10) + "," + (v % 10); }

    private String decode(byte[] f) {
        final int d = 3;
        int len = f[2] & 0xff;
        int type = f[1] & 0xff;
        switch (type) {
            case 0x33:
                if (len < 6) return null;
                int ci = u16(f, d), au = u16(f, d + 2), de = u16(f, d + 4);
                vConsoInst = ci > 300 ? "--" : x10(ci) + " L/100";
                vAutonomie = au > 2000 ? "--" : au + " km";
                vDest = de > 6000 ? "--" : de + " km";
                return "conso instantanée brute=" + ci + " (" + vConsoInst + ")"
                        + " | AUTONOMIE brute=" + au + " → " + vAutonomie
                        + " | distance destination=" + vDest;
            case 0x34:
            case 0x35:
                if (len < 6) return null;
                int cm = u16(f, d), vm = u16(f, d + 2), tr = u16(f, d + 4);
                String sCm = cm > 300 ? "--" : x10(cm) + " L/100";
                String sVm = vm > 250 ? "--" : vm + " km/h";
                String sTr = tr > 10000 ? "--" : tr + " km";
                if (type == 0x34) { vConsoMoy1 = sCm; vVitMoy1 = sVm; vTrajet1 = sTr; }
                else { vConsoMoy2 = sCm; vVitMoy2 = sVm; vTrajet2 = sTr; }
                return "trajet " + (type - 0x33) + " : conso moy. brute=" + cm + " (" + sCm + ")"
                        + " | vitesse moy.=" + sVm + " | distance=" + sTr;
            case 0x36:
                if (len < 1) return null;
                int v = f[d] & 0xff;
                int temp = (v & 0x80) != 0 ? -(v & 0x7f) : (v & 0x7f);
                vTemp = temp + " °C";
                return "température extérieure=" + vTemp;
            default:
                return null;
        }
    }

    String summary() {
        return "AUTONOMIE " + vAutonomie + " | conso inst. " + vConsoInst
                + " | trajet1 " + vTrajet1 + ", " + vConsoMoy1 + ", " + vVitMoy1
                + " | trajet2 " + vTrajet2 + ", " + vConsoMoy2 + ", " + vVitMoy2
                + " | ext. " + vTemp;
    }

    private static String typeName(int t) {
        switch (t) {
            case 0x02: return "touches volant";
            case 0x21: return "clim";
            case 0x29: return "angle volant";
            case 0x30: return "radars AR";
            case 0x32: return "radars";
            case 0x33: return "ordi de bord page 0";
            case 0x34: return "trajet 1";
            case 0x35: return "trajet 2";
            case 0x36: return "temp. ext.";
            case 0x38: return "portes";
            case 0x3A: return "alertes";
            case 0x3B: return "véhicule";
            case 0x3D: return "véhicule 2";
            case 0x7F: return "version boîtier";
            default: return "?";
        }
    }

    // ------------------------------------------------------------------ outils

    private static String sig(Method m) {
        StringBuilder sb = new StringBuilder("(");
        Class<?>[] p = m.getParameterTypes();
        for (int i = 0; i < p.length; i++) {
            if (i > 0) sb.append(", ");
            sb.append(p[i].getSimpleName());
        }
        return sb.append(")").toString();
    }

    static String hex(byte[] a) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < a.length && i < 200; i++) sb.append(String.format("%02X ", a[i]));
        if (a.length > 200) sb.append("…");
        return sb.toString().trim();
    }

    private static String ascii(byte[] a) {
        StringBuilder sb = new StringBuilder();
        for (byte x : a) sb.append(x >= 32 && x < 127 ? (char) x : '.');
        return sb.toString();
    }

    private static String root(Throwable t) {
        while (t.getCause() != null) t = t.getCause();
        return t.toString();
    }

    private static byte[] readAll(java.io.InputStream in) throws java.io.IOException {
        try (java.io.InputStream is = in) {
            ByteArrayOutputStream bo = new ByteArrayOutputStream();
            byte[] buf = new byte[65536];
            int r;
            while ((r = is.read(buf)) > 0) bo.write(buf, 0, r);
            return bo.toByteArray();
        }
    }

    private static int indexOf(byte[] h, byte[] n) {
        outer:
        for (int i = 0; i + n.length <= h.length; i++) {
            for (int j = 0; j < n.length; j++) if (h[i + j] != n[j]) continue outer;
            return i;
        }
        return -1;
    }
}
