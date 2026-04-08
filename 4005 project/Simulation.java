import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Random;
import java.util.stream.*;
import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.GradientPaint;
import java.awt.Graphics2D;
import java.awt.GraphicsEnvironment;
import java.awt.RenderingHints;
import java.awt.image.BufferedImage;
import javax.swing.*;
import java.io.File;
import java.io.IOException;
import javax.imageio.ImageIO;

/**
 * SYSC4005/5001 – Simulation & Modeling Project (Winter 2026)
 * Two-Node Computer Processing System
 *
 * Fixes applied vs original:
 * 1. tryStartN1v2 slot-switching: advances slotExpiry from its previous value
 * (using a while loop) so idle time correctly counts against the current slot.
 * 2. avgSystemB1/B2: uses exact tracked per-type in-service area instead of
 * an approximate proportional split.
 * 3. Histograms rendered as PNG images using built-in Java2D (no external
 * libs).
 * PNGs saved to ./histograms/ and displayed in a tabbed Swing window.
 *
 * System requirements:
 * - Buffer 1 (Type I): Poisson arrivals, mean IAT = 4ms, service Uniform[1,3]ms
 * - Buffer 2 (Type II): Poisson arrivals, mean IAT = 12ms, service
 * Uniform[2,6]ms
 * - Processing Node 1: Alternates 50ms on B1 / 30ms on B2; skips empty buffer
 * - Router 1: Redirects packet if Node-2 queue length > 5
 * - Processing Node 2: 2 parallel processors, Exp(mean=5ms) each, common buffer
 * - Type II routing: p=0.5 to Node 2, p=0.5 discarded
 */
public class Simulation {

    // ─── Simulation parameters ───────────────────────────────────────────────
    static final double SIM_TIME = 5_000_000; // ms
    static final double MEAN_IAT_B1 = 4.0;
    static final double MEAN_IAT_B2 = 12.0;
    static final double UNIF_B1_LO = 1.0, UNIF_B1_HI = 3.0; // mean = 2ms
    static final double UNIF_B2_LO = 2.0, UNIF_B2_HI = 6.0; // mean = 4ms
    static final double MEAN_SVC_N2 = 5.0;
    static final double SLOT_B1 = 50.0;
    static final double SLOT_B2 = 30.0;
    static final int ROUTER_THRESH = 5; // redirect if N2 queue length > 5
    static final double TYPE2_FWD_PROB = 0.5;
    static final int NUM_REPLICATIONS = 30;

    // ─── Event types ─────────────────────────────────────────────────────────
    static final int EVT_ARRIVE_B1 = 1;
    static final int EVT_ARRIVE_B2 = 2;
    static final int EVT_N1_DONE = 3;
    static final int EVT_N2_DONE = 4;

    // ─── RNG ─────────────────────────────────────────────────────────────────
    static Random rng = new Random();

    static double expRand(double mean) {
        return -mean * Math.log(1 - rng.nextDouble());
    }

    static double uniformRand(double lo, double hi) {
        return lo + rng.nextDouble() * (hi - lo);
    }

    // =========================================================================
    // Packet
    // =========================================================================
    static class Packet {
        int type;
        double arrivalTime;
        double serviceStartN1;
        double departN1;
        double arrivalN2;
        double serviceStartN2;
        double departN2;
        boolean redirected;

        Packet(int type, double t) {
            this.type = type;
            this.arrivalTime = t;
        }

        double waitInBuffer() {
            return serviceStartN1 - arrivalTime;
        }

        double sojourn1() {
            return departN1 - arrivalTime;
        }

        double sojournN2() {
            return departN2 - arrivalN2;
        }
    }

    // =========================================================================
    // Event
    // =========================================================================
    static class Event implements Comparable<Event> {
        double time;
        int type;
        Object data;

        Event(double t, int type, Object data) {
            this.time = t;
            this.type = type;
            this.data = data;
        }

        @Override
        public int compareTo(Event o) {
            return Double.compare(this.time, o.time);
        }
    }

    // =========================================================================
    // Per-replication statistics
    // =========================================================================
    static class Stats {
        int arrivedB1, arrivedB2;
        int redirected;
        int type2Forwarded, type2Discarded;
        int servedN1, servedN2;

        // Area-under-curve (time-average queue lengths)
        double areaB1 = 0, areaB2 = 0;
        double areaN1InService = 0;
        double areaN2Queue = 0, areaN2InService = 0;

        // FIX 2: track in-service area separately per type for exact (a)/(b)
        double areaN1InSvcT1 = 0;
        double areaN1InSvcT2 = 0;

        // Sample lists
        List<Double> waitB1 = new ArrayList<>();
        List<Double> waitB2 = new ArrayList<>();
        List<Double> sojourn1_T1 = new ArrayList<>();
        List<Double> sojourn1_T2 = new ArrayList<>();
        List<Double> sojournN2 = new ArrayList<>();

        // Derived metrics
        double avgSystemB1, avgSystemB2;
        double avgWaitB1, avgWaitB2;
        double avgSojourn1_T1, avgSojourn1_T2;
        double avgSojournN2;
        double pRedirect;
        double fracWaitB1, fracWaitB2;
        double avgNumWaitB1, avgNumWaitB2;
    }

    // =========================================================================
    // Run one replication
    // =========================================================================
    static Stats runReplication(long seed) {
        rng = new Random(seed);
        Stats st = new Stats();

        Queue<Packet> queueB1 = new LinkedList<>();
        Queue<Packet> queueB2 = new LinkedList<>();
        Queue<Packet> queueN2 = new LinkedList<>();

        boolean n1Busy = false;
        Packet n1CurrentPacket = null;

        // FIX 1: slotExpiry is a wall-clock deadline initialised at sim start.
        // It will be advanced from its previous value (not from clock) in
        // tryStartN1v2, so idle periods correctly consume the current slot budget.
        int n1ActiveBuffer = 1;
        double n1SlotExpiry = SLOT_B1;

        Packet[] n2Proc = new Packet[2];

        double prevTime = 0;
        int lenB1 = 0, lenB2 = 0, n1InSvc = 0, lenN2Q = 0, n2InSvc = 0;
        int n1CurrentType = 0; // type of packet currently in service at N1

        PriorityQueue<Event> evq = new PriorityQueue<>();
        evq.add(new Event(expRand(MEAN_IAT_B1), EVT_ARRIVE_B1, null));
        evq.add(new Event(expRand(MEAN_IAT_B2), EVT_ARRIVE_B2, null));

        double clock = 0;

        while (!evq.isEmpty()) {
            Event evt = evq.poll();
            clock = evt.time;
            if (clock > SIM_TIME)
                break;

            // Accumulate area
            double dt = clock - prevTime;
            st.areaB1 += dt * lenB1;
            st.areaB2 += dt * lenB2;
            st.areaN1InService += dt * n1InSvc;
            st.areaN2Queue += dt * lenN2Q;
            st.areaN2InService += dt * n2InSvc;
            // FIX 2: per-type in-service area
            if (n1InSvc == 1) {
                if (n1CurrentType == 1)
                    st.areaN1InSvcT1 += dt;
                else
                    st.areaN1InSvcT2 += dt;
            }
            prevTime = clock;

            switch (evt.type) {

                // ── Arrival at Buffer 1 ──────────────────────────────────────
                case EVT_ARRIVE_B1: {
                    Packet p = new Packet(1, clock);
                    st.arrivedB1++;
                    queueB1.add(p);
                    lenB1++;
                    evq.add(new Event(clock + expRand(MEAN_IAT_B1), EVT_ARRIVE_B1, null));
                    if (!n1Busy) {
                        boolean started = tryStartN1v2(clock, queueB1, queueB2,
                                n1ActiveBuffer, n1SlotExpiry, evq);
                        if (started) {
                            n1Busy = true;
                            n1InSvc = 1;
                            Object[] s = lastStartResult;
                            n1CurrentPacket = (Packet) s[0];
                            n1ActiveBuffer = (int) s[1];
                            n1SlotExpiry = (double) s[2];
                            n1CurrentType = n1CurrentPacket.type;
                            lenB1 = queueB1.size();
                            lenB2 = queueB2.size();
                        }
                    }
                    break;
                }

                // ── Arrival at Buffer 2 ──────────────────────────────────────
                case EVT_ARRIVE_B2: {
                    Packet p = new Packet(2, clock);
                    st.arrivedB2++;
                    queueB2.add(p);
                    lenB2++;
                    evq.add(new Event(clock + expRand(MEAN_IAT_B2), EVT_ARRIVE_B2, null));
                    if (!n1Busy) {
                        boolean started = tryStartN1v2(clock, queueB1, queueB2,
                                n1ActiveBuffer, n1SlotExpiry, evq);
                        if (started) {
                            n1Busy = true;
                            n1InSvc = 1;
                            Object[] s = lastStartResult;
                            n1CurrentPacket = (Packet) s[0];
                            n1ActiveBuffer = (int) s[1];
                            n1SlotExpiry = (double) s[2];
                            n1CurrentType = n1CurrentPacket.type;
                            lenB1 = queueB1.size();
                            lenB2 = queueB2.size();
                        }
                    }
                    break;
                }

                // ── Node 1 finishes ──────────────────────────────────────────
                case EVT_N1_DONE: {
                    Object[] info = (Object[]) evt.data;
                    Packet p = (Packet) info[0];
                    n1ActiveBuffer = (int) info[1];
                    n1SlotExpiry = (double) info[2];

                    p.departN1 = clock;
                    st.servedN1++;

                    if (p.type == 1)
                        st.sojourn1_T1.add(p.sojourn1());
                    else
                        st.sojourn1_T2.add(p.sojourn1());

                    double w = p.waitInBuffer();
                    if (p.type == 1)
                        st.waitB1.add(w);
                    else
                        st.waitB2.add(w);

                    // ── Route the packet ────────────────────────────────────
                    boolean forward;
                    if (p.type == 1) {
                        forward = true;
                    } else {
                        forward = rng.nextDouble() < TYPE2_FWD_PROB;
                        if (!forward)
                            st.type2Discarded++;
                        else
                            st.type2Forwarded++;
                    }

                    if (forward) {
                        if (lenN2Q > ROUTER_THRESH) {
                            p.redirected = true;
                            st.redirected++;
                        } else {
                            p.arrivalN2 = clock;
                            queueN2.add(p);
                            lenN2Q++;
                            for (int i = 0; i < 2; i++) {
                                if (n2Proc[i] == null && !queueN2.isEmpty()) {
                                    Packet np = queueN2.poll();
                                    lenN2Q--;
                                    np.serviceStartN2 = clock;
                                    n2Proc[i] = np;
                                    n2InSvc++;
                                    evq.add(new Event(clock + expRand(MEAN_SVC_N2),
                                            EVT_N2_DONE, new Object[] { np, i }));
                                }
                            }
                        }
                    }

                    // ── Start next packet at Node 1 ─────────────────────────
                    n1Busy = false;
                    n1InSvc = 0;
                    n1CurrentPacket = null;
                    n1CurrentType = 0;
                    boolean started = tryStartN1v2(clock, queueB1, queueB2,
                            n1ActiveBuffer, n1SlotExpiry, evq);
                    if (started) {
                        n1Busy = true;
                        n1InSvc = 1;
                        Object[] s = lastStartResult;
                        n1CurrentPacket = (Packet) s[0];
                        n1ActiveBuffer = (int) s[1];
                        n1SlotExpiry = (double) s[2];
                        n1CurrentType = n1CurrentPacket.type;
                        lenB1 = queueB1.size();
                        lenB2 = queueB2.size();
                    }
                    break;
                }

                // ── Node 2 processor finishes ────────────────────────────────
                case EVT_N2_DONE: {
                    Object[] info = (Object[]) evt.data;
                    Packet p = (Packet) info[0];
                    int pid = (int) info[1];

                    p.departN2 = clock;
                    st.servedN2++;
                    st.sojournN2.add(p.sojournN2());

                    n2Proc[pid] = null;
                    n2InSvc--;

                    if (!queueN2.isEmpty()) {
                        Packet np = queueN2.poll();
                        lenN2Q--;
                        np.serviceStartN2 = clock;
                        n2Proc[pid] = np;
                        n2InSvc++;
                        evq.add(new Event(clock + expRand(MEAN_SVC_N2),
                                EVT_N2_DONE, new Object[] { np, pid }));
                    }
                    break;
                }
            }
        }

        // ── Final area update ────────────────────────────────────────────────
        double dt = SIM_TIME - prevTime;
        st.areaB1 += dt * lenB1;
        st.areaB2 += dt * lenB2;
        st.areaN1InService += dt * n1InSvc;
        st.areaN2Queue += dt * lenN2Q;
        st.areaN2InService += dt * n2InSvc;
        if (n1InSvc == 1) {
            if (n1CurrentType == 1)
                st.areaN1InSvcT1 += dt;
            else
                st.areaN1InSvcT2 += dt;
        }

        // ── Compute derived metrics ──────────────────────────────────────────
        double avgQB1 = st.areaB1 / SIM_TIME;
        double avgQB2 = st.areaB2 / SIM_TIME;
        st.avgNumWaitB1 = avgQB1;
        st.avgNumWaitB2 = avgQB2;

        // FIX 2: exact per-type in-service area (no approximation)
        st.avgSystemB1 = avgQB1 + st.areaN1InSvcT1 / SIM_TIME;
        st.avgSystemB2 = avgQB2 + st.areaN1InSvcT2 / SIM_TIME;

        long waitedB1 = st.waitB1.stream().filter(w -> w > 1e-9).count();
        long waitedB2 = st.waitB2.stream().filter(w -> w > 1e-9).count();
        st.fracWaitB1 = st.waitB1.isEmpty() ? 0 : (double) waitedB1 / st.waitB1.size();
        st.fracWaitB2 = st.waitB2.isEmpty() ? 0 : (double) waitedB2 / st.waitB2.size();

        st.avgWaitB1 = st.waitB1.stream().mapToDouble(d -> d).average().orElse(0);
        st.avgWaitB2 = st.waitB2.stream().mapToDouble(d -> d).average().orElse(0);
        st.avgSojourn1_T1 = st.sojourn1_T1.stream().mapToDouble(d -> d).average().orElse(0);
        st.avgSojourn1_T2 = st.sojourn1_T2.stream().mapToDouble(d -> d).average().orElse(0);
        st.avgSojournN2 = st.sojournN2.stream().mapToDouble(d -> d).average().orElse(0);

        int reachedRouter = st.servedN2 + st.redirected;
        st.pRedirect = reachedRouter > 0 ? (double) st.redirected / reachedRouter : 0;

        return st;
    }

    // =========================================================================
    // tryStartN1v2 – attempt to start the next packet at Node 1.
    //
    // FIX 1: Slot expiry is advanced from its *previous* value using a while loop,
    // so idle time is charged against the current slot, not the next one.
    // Updated state is returned via lastStartResult = [packet, activeBuffer,
    // slotExpiry].
    // =========================================================================
    static Object[] lastStartResult = null;

    static boolean tryStartN1v2(double clock,
            Queue<Packet> qB1, Queue<Packet> qB2,
            int activeBuffer, double slotExpiry,
            PriorityQueue<Event> evq) {

        // FIX 1: advance slotExpiry forward from its previous value so idle
        // time correctly consumes the current slot's budget.
        while (clock >= slotExpiry) {
            activeBuffer = (activeBuffer == 1) ? 2 : 1;
            slotExpiry += (activeBuffer == 1 ? SLOT_B1 : SLOT_B2);
        }

        Packet p = null;
        if (activeBuffer == 1) {
            if (!qB1.isEmpty())
                p = qB1.poll();
            else if (!qB2.isEmpty())
                p = qB2.poll();
        } else {
            if (!qB2.isEmpty())
                p = qB2.poll();
            else if (!qB1.isEmpty())
                p = qB1.poll();
        }

        if (p == null)
            return false;

        double svcTime = (p.type == 1) ? uniformRand(UNIF_B1_LO, UNIF_B1_HI)
                : uniformRand(UNIF_B2_LO, UNIF_B2_HI);
        p.serviceStartN1 = clock;

        Event e = new Event(clock + svcTime, EVT_N1_DONE,
                new Object[] { p, activeBuffer, slotExpiry });
        evq.add(e);
        lastStartResult = new Object[] { p, activeBuffer, slotExpiry };
        return true;
    }

    // =========================================================================
    // Statistical helpers (95% CI, t(29) = 2.045)
    // =========================================================================
    static final double T_CRIT = 2.045;

    static double mean(double[] x) {
        double s = 0;
        for (double v : x)
            s += v;
        return s / x.length;
    }

    static double variance(double[] x, double m) {
        double s = 0;
        for (double v : x)
            s += (v - m) * (v - m);
        return s / (x.length - 1);
    }

    static double ci(double[] x) {
        double m = mean(x);
        double s = Math.sqrt(variance(x, m));
        return T_CRIT * s / Math.sqrt(x.length);
    }

    static void printCI(String label, double[] x) {
        double m = mean(x);
        double hw = ci(x);
        System.out.printf("  %-55s  %.5f  ±  %.5f%n", label, m, hw);
        System.out.printf("  %55s  95%% CI: [%.5f, %.5f]%n", "", m - hw, m + hw);
    }

    // =========================================================================
    // Console histogram (kept for terminal output)
    // =========================================================================
    static void printHistogram(String title, List<Double> data, int bins) {
        if (data.isEmpty()) {
            System.out.println("  (no data)");
            return;
        }
        double min = data.stream().mapToDouble(d -> d).min().getAsDouble();
        double max = data.stream().mapToDouble(d -> d).max().getAsDouble();
        if (max == min)
            max = min + 1;
        double width = (max - min) / bins;
        int[] counts = new int[bins];
        for (double v : data) {
            int b = (int) ((v - min) / width);
            if (b >= bins)
                b = bins - 1;
            counts[b]++;
        }
        System.out.printf("%n  Histogram: %s (n=%d, min=%.3f, max=%.3f)%n",
                title, data.size(), min, max);
        System.out.printf("  %-14s %-10s %s%n", "Bin range", "Count", "Bar");
        int maxCount = Arrays.stream(counts).max().getAsInt();
        for (int i = 0; i < bins; i++) {
            double lo = min + i * width;
            double hi = lo + width;
            int bar = maxCount > 0 ? (int) (40.0 * counts[i] / maxCount) : 0;
            System.out.printf("  [%6.2f,%6.2f) %-10d %s%n",
                    lo, hi, counts[i], "#".repeat(bar));
        }
    }

    // =========================================================================
    // Distribution fitting via coefficient of variation
    // =========================================================================
    static void testDistribution(String label, List<Double> data) {
        if (data.size() < 30) {
            System.out.println("  Not enough data.");
            return;
        }
        double m = data.stream().mapToDouble(d -> d).average().orElse(1);
        double v = data.stream().mapToDouble(d -> d).map(x -> (x - m) * (x - m)).average().orElse(1);
        double cv = Math.sqrt(v) / m;
        System.out.printf("  Distribution test [%s]: mean=%.4f  std=%.4f  CV=%.4f%n",
                label, m, Math.sqrt(v), cv);
        System.out.println("  Fit guidance (based on CV):");
        if (Math.abs(cv - 1.0) < 0.15) {
            System.out.println("   → CV ≈ 1 → consistent with Exponential distribution");
            System.out.printf("   → Fitted Exp(λ=%.4f), mean=%.4f ms%n", 1 / m, m);
        } else if (cv > 0.55 && cv < 0.85) {
            System.out.println("   → CV ≈ 0.71 → consistent with Erlang-2 (k=2) distribution");
            System.out.printf("   → Fitted Erlang-2(μ=%.4f per stage), overall mean=%.4f ms%n", 2 / m, m);
        } else if (cv < 0.2) {
            System.out.println("   → CV ≈ 0 → consistent with Deterministic / near-uniform distribution");
        } else if (cv > 1.1) {
            System.out.println("   → CV > 1 → heavy-tailed; may fit Hyper-Exponential");
        } else {
            System.out.printf("   → CV=%.3f; does not clearly match standard distributions%n", cv);
        }
    }

    // =========================================================================
    // Graphical histogram: Java2D rendering, no external libraries required.
    //
    // Each chart is saved as a PNG to ./histograms/ and shown in a tabbed
    // Swing window. Works on any JDK 8+ with a display; gracefully falls back
    // to PNG-only in headless (server) environments.
    // =========================================================================

    private static final Color[] PALETTE = {
            new Color(0x4C72B0), // blue
            new Color(0xDD8452), // orange
            new Color(0x55A868), // green
            new Color(0xC44E52), // red
            new Color(0x8172B2) // purple
    };

    /**
     * Build a polished BufferedImage histogram from raw sample data.
     *
     * @param title    Chart title (shown at top)
     * @param data     Raw samples
     * @param bins     Number of histogram bins
     * @param xLabel   X-axis label string
     * @param barColor Bar fill colour
     * @param meanVal  Mean value — drawn as a dashed red reference line
     */
    static BufferedImage buildHistogramImage(String title, List<Double> data,
            int bins, String xLabel,
            Color barColor, double meanVal) {
        final int W = 820, H = 520;
        final int PAD_L = 80, PAD_R = 30, PAD_T = 60, PAD_B = 72;
        int chartW = W - PAD_L - PAD_R;
        int chartH = H - PAD_T - PAD_B;

        BufferedImage img = new BufferedImage(W, H, BufferedImage.TYPE_INT_RGB);
        Graphics2D g = img.createGraphics();
        g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_ON);

        // Background
        g.setColor(new Color(0xF8F8F8));
        g.fillRect(0, 0, W, H);
        // Plot area background
        g.setColor(new Color(0xEAEAEA));
        g.fillRect(PAD_L, PAD_T, chartW, chartH);

        // ── Bin the data ─────────────────────────────────────────────────────
        double minV = data.stream().mapToDouble(d -> d).min().orElse(0);
        double maxV = data.stream().mapToDouble(d -> d).max().orElse(1);
        if (maxV == minV)
            maxV = minV + 1;
        double binW = (maxV - minV) / bins;
        int[] counts = new int[bins];
        for (double v : data) {
            int b = (int) ((v - minV) / binW);
            if (b >= bins)
                b = bins - 1;
            counts[b]++;
        }
        int maxCount = Arrays.stream(counts).max().orElse(1);

        // ── Horizontal grid lines + Y-axis tick labels ────────────────────────
        Font labelFont = new Font("SansSerif", Font.PLAIN, 11);
        Font boldFont = new Font("SansSerif", Font.BOLD, 12);
        Font titleFont = new Font("SansSerif", Font.BOLD, 14);
        g.setFont(labelFont);
        FontMetrics fm = g.getFontMetrics();
        int nYTicks = 5;
        for (int i = 0; i <= nYTicks; i++) {
            int y = PAD_T + chartH - (int) (chartH * i / (double) nYTicks);
            g.setColor(Color.WHITE);
            g.setStroke(new BasicStroke(1f));
            g.drawLine(PAD_L, y, PAD_L + chartW, y);
            long tickVal = Math.round((long) maxCount * i / (double) nYTicks);
            String lbl = formatCount(tickVal);
            g.setColor(new Color(0x444444));
            g.drawString(lbl, PAD_L - fm.stringWidth(lbl) - 6, y + fm.getAscent() / 2 - 1);
        }

        // ── Bars with gradient fill ───────────────────────────────────────────
        double barWidthPx = (double) chartW / bins;
        for (int i = 0; i < bins; i++) {
            int barH = (int) (chartH * counts[i] / (double) maxCount);
            int bx = PAD_L + (int) (i * barWidthPx);
            int by = PAD_T + chartH - barH;
            int bw = Math.max(1, (int) barWidthPx - 1);

            // Drop shadow
            g.setColor(new Color(0, 0, 0, 20));
            g.fillRect(bx + 2, by + 2, bw, barH);
            // Gradient fill
            if (barH > 0) {
                GradientPaint gp = new GradientPaint(bx, by, barColor.brighter(),
                        bx, by + barH, barColor.darker());
                g.setPaint(gp);
                g.fillRect(bx, by, bw, barH);
            }
            // Outline
            g.setColor(barColor.darker().darker());
            g.setStroke(new BasicStroke(0.5f));
            g.drawRect(bx, by, bw, barH);
        }

        // ── Mean reference line ───────────────────────────────────────────────
        if (meanVal >= minV && meanVal <= maxV) {
            int mx = PAD_L + (int) (chartW * (meanVal - minV) / (maxV - minV));
            g.setColor(new Color(0xD32F2F));
            float[] dash = { 7f, 4f };
            g.setStroke(new BasicStroke(2f, BasicStroke.CAP_BUTT,
                    BasicStroke.JOIN_MITER, 10f, dash, 0f));
            g.drawLine(mx, PAD_T, mx, PAD_T + chartH);
            g.setFont(new Font("SansSerif", Font.BOLD | Font.ITALIC, 11));
            g.setColor(new Color(0xB71C1C));
            String meanLabel = String.format("μ = %.2f ms", meanVal);
            g.drawString(meanLabel, mx + 5, PAD_T + 16);
            g.setFont(labelFont);
        }

        // ── Axes ─────────────────────────────────────────────────────────────
        g.setColor(new Color(0x333333));
        g.setStroke(new BasicStroke(1.5f));
        g.drawLine(PAD_L, PAD_T, PAD_L, PAD_T + chartH);
        g.drawLine(PAD_L, PAD_T + chartH, PAD_L + chartW, PAD_T + chartH);

        // ── X-axis tick labels ────────────────────────────────────────────────
        g.setFont(labelFont);
        g.setColor(new Color(0x444444));
        int tickEvery = Math.max(1, bins / 7);
        for (int i = 0; i <= bins; i += tickEvery) {
            double val = minV + i * binW;
            String lbl = String.format("%.1f", val);
            int tx = PAD_L + (int) (chartW * i / (double) bins);
            g.setColor(new Color(0x333333));
            g.setStroke(new BasicStroke(1f));
            g.drawLine(tx, PAD_T + chartH, tx, PAD_T + chartH + 4);
            g.setColor(new Color(0x444444));
            g.drawString(lbl, tx - fm.stringWidth(lbl) / 2, PAD_T + chartH + 17);
        }

        // ── Axis labels ───────────────────────────────────────────────────────
        g.setFont(boldFont);
        FontMetrics bfm = g.getFontMetrics();
        // X axis label
        String xlbl = xLabel + "  (n = " + formatCount(data.size()) + ")";
        g.setColor(new Color(0x333333));
        g.drawString(xlbl, PAD_L + chartW / 2 - bfm.stringWidth(xlbl) / 2, H - 10);
        // Y axis label (rotated)
        Graphics2D gr = img.createGraphics();
        gr.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        gr.setFont(boldFont);
        gr.setColor(new Color(0x333333));
        gr.rotate(-Math.PI / 2);
        gr.drawString("Frequency", -(PAD_T + chartH / 2 + 30), 18);
        gr.dispose();

        // ── Title ─────────────────────────────────────────────────────────────
        g.setFont(titleFont);
        FontMetrics tfm = g.getFontMetrics();
        g.setColor(new Color(0x1A237E));
        g.drawString(title, PAD_L + chartW / 2 - tfm.stringWidth(title) / 2, PAD_T - 20);

        // ── Outer border ──────────────────────────────────────────────────────
        g.setColor(new Color(0xBBBBBB));
        g.setStroke(new BasicStroke(1f));
        g.drawRect(0, 0, W - 1, H - 1);

        g.dispose();
        return img;
    }

    /** Format large counts compactly: 1_200_000 → "1.2M" */
    private static String formatCount(long n) {
        if (n >= 1_000_000)
            return String.format("%.1fM", n / 1_000_000.0);
        else if (n >= 1_000)
            return String.format("%.1fK", n / 1_000.0);
        else
            return Long.toString(n);
    }

    /**
     * Render all five histograms, save them as PNGs, and open a Swing window.
     */
    static void showAndSaveHistograms(List<Double> waitB1, List<Double> waitB2,
            List<Double> soj1T1, List<Double> soj1T2,
            List<Double> sojN2) {
        double mWB1 = waitB1.stream().mapToDouble(d -> d).average().orElse(0);
        double mWB2 = waitB2.stream().mapToDouble(d -> d).average().orElse(0);
        double mS1T1 = soj1T1.stream().mapToDouble(d -> d).average().orElse(0);
        double mS1T2 = soj1T2.stream().mapToDouble(d -> d).average().orElse(0);
        double mSN2 = sojN2.stream().mapToDouble(d -> d).average().orElse(0);

        String[][] specs = {
                { "(e) Buffer 1 Wait – Type I", "Wait time (ms)" },
                { "(e) Buffer 2 Wait – Type II", "Wait time (ms)" },
                { "(f) N1 Sojourn – Type I", "Sojourn time (ms)" },
                { "(f) N1 Sojourn – Type II", "Sojourn time (ms)" },
                { "(g) N2 Station Sojourn", "Sojourn time (ms)" },
        };
        @SuppressWarnings("unchecked")
        List<Double>[] datasets = new List[] { waitB1, waitB2, soj1T1, soj1T2, sojN2 };
        double[] means = { mWB1, mWB2, mS1T1, mS1T2, mSN2 };

        // Save PNGs to ./histograms/
        File dir = new File("histograms");
        dir.mkdirs();
        BufferedImage[] images = new BufferedImage[5];
        for (int i = 0; i < 5; i++) {
            images[i] = buildHistogramImage(specs[i][0], datasets[i],
                    20, specs[i][1], PALETTE[i], means[i]);
            String fname = "histograms/hist_" + (char) ('a' + i) + "_" +
                    specs[i][0].replaceAll("[^a-zA-Z0-9]", "_").replaceAll("_+", "_") + ".png";
            try {
                ImageIO.write(images[i], "PNG", new File(fname));
                System.out.println("  Saved: " + fname);
            } catch (IOException ex) {
                System.err.println("  Could not save " + fname + ": " + ex.getMessage());
            }
        }

        // Display in Swing window (skipped if no display is available)
        if (GraphicsEnvironment.isHeadless()) {
            System.out.println("  (Headless environment – PNGs saved to ./histograms/)");
            return;
        }
        SwingUtilities.invokeLater(() -> {
            JFrame frame = new JFrame("SYSC4005/5001 – Simulation Histograms");
            frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
            JTabbedPane tabs = new JTabbedPane();
            tabs.setFont(new Font("SansSerif", Font.PLAIN, 12));
            for (int i = 0; i < 5; i++) {
                JLabel lbl = new JLabel(new ImageIcon(images[i]));
                lbl.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10));
                tabs.addTab(specs[i][0], new JScrollPane(lbl));
            }
            frame.add(tabs);
            frame.pack();
            frame.setLocationRelativeTo(null);
            frame.setVisible(true);
        });
    }

    // =========================================================================
    // Main
    // =========================================================================
    public static void main(String[] args) {
        System.out.println("=".repeat(70));
        System.out.println("  SYSC4005/5001 - Simulation & Modeling Project  (Winter 2026)");
        System.out.println("  Two-Node Computer Processing System");
        System.out.printf("  Replications: %d   Simulation time per run: %.0f ms%n",
                NUM_REPLICATIONS, SIM_TIME);
        System.out.println("=".repeat(70));

        double[] avgSystemB1 = new double[NUM_REPLICATIONS];
        double[] avgSystemB2 = new double[NUM_REPLICATIONS];
        double[] fracWaitB1 = new double[NUM_REPLICATIONS];
        double[] fracWaitB2 = new double[NUM_REPLICATIONS];
        double[] avgNumWaitB1 = new double[NUM_REPLICATIONS];
        double[] avgNumWaitB2 = new double[NUM_REPLICATIONS];
        double[] avgWaitB1 = new double[NUM_REPLICATIONS];
        double[] avgWaitB2 = new double[NUM_REPLICATIONS];
        double[] avgSoj1_T1 = new double[NUM_REPLICATIONS];
        double[] avgSoj1_T2 = new double[NUM_REPLICATIONS];
        double[] avgSojN2 = new double[NUM_REPLICATIONS];
        double[] pRedirect = new double[NUM_REPLICATIONS];

        List<Double> allWaitB1 = null, allWaitB2 = null;
        List<Double> allSoj1T1 = null, allSoj1T2 = null, allSojN2 = null;

        System.out.println("\nRunning replications...");
        for (int r = 0; r < NUM_REPLICATIONS; r++) {
            Stats st = runReplication(r * 12345L + 7919L);
            avgSystemB1[r] = st.avgSystemB1;
            avgSystemB2[r] = st.avgSystemB2;
            fracWaitB1[r] = st.fracWaitB1;
            fracWaitB2[r] = st.fracWaitB2;
            avgNumWaitB1[r] = st.avgNumWaitB1;
            avgNumWaitB2[r] = st.avgNumWaitB2;
            avgWaitB1[r] = st.avgWaitB1;
            avgWaitB2[r] = st.avgWaitB2;
            avgSoj1_T1[r] = st.avgSojourn1_T1;
            avgSoj1_T2[r] = st.avgSojourn1_T2;
            avgSojN2[r] = st.avgSojournN2;
            pRedirect[r] = st.pRedirect;
            if (r == NUM_REPLICATIONS - 1) {
                allWaitB1 = st.waitB1;
                allWaitB2 = st.waitB2;
                allSoj1T1 = st.sojourn1_T1;
                allSoj1T2 = st.sojourn1_T2;
                allSojN2 = st.sojournN2;
            }
            System.out.printf("  Rep %2d: avgSysB1=%.3f  avgSysB2=%.3f  pRedir=%.4f%n",
                    r + 1, avgSystemB1[r], avgSystemB2[r], pRedirect[r]);
        }

        // ── Results table ─────────────────────────────────────────────────────
        System.out.println("\n" + "=".repeat(70));
        System.out.println("  RESULTS  (95% Confidence Intervals)");
        System.out.println("=".repeat(70));
        printCI("(a) Avg # Type-I pkts in Buffer1 + being served by N1", avgSystemB1);
        printCI("(b) Avg # Type-II pkts in Buffer2 + being served by N1", avgSystemB2);
        printCI("(c) Avg # Type-I pkts waiting in Buffer1", avgNumWaitB1);
        printCI("(d) Avg # Type-II pkts waiting in Buffer2", avgNumWaitB2);

        printCI("(c-alt) Fraction of Type-I pkts that waited", fracWaitB1);
        printCI("(d-alt) Fraction of Type-II pkts that waited", fracWaitB2);

        System.out.println("\n--- (e) Average waiting time in buffers ---");
        printCI("    Avg waiting time in Buffer 1 (ms)", avgWaitB1);
        printCI("    Avg waiting time in Buffer 2 (ms)", avgWaitB2);

        System.out.println("\n--- (f) Average sojourn time at Node-1 station ---");
        printCI("    Type-I  sojourn at N1 (wait + service, ms)", avgSoj1_T1);
        printCI("    Type-II sojourn at N1 (wait + service, ms)", avgSoj1_T2);

        System.out.println("\n--- (g) Average sojourn time at Node-2 station ---");
        printCI("    Sojourn at N2 station (wait + service, ms)", avgSojN2);

        System.out.println("\n--- (h) Redirect probability (Router 1) ---");
        printCI("    P(packet redirected by Router 1)", pRedirect);

        // ── Console histograms ────────────────────────────────────────────────
        System.out.println("\n" + "=".repeat(70));
        System.out.println("  HISTOGRAMS  (text, from last replication)");
        System.out.println("=".repeat(70));
        printHistogram("(e) Waiting time - Buffer 1 (Type I)", allWaitB1, 15);
        printHistogram("(e) Waiting time - Buffer 2 (Type II)", allWaitB2, 15);
        printHistogram("(f) Sojourn time at N1 - Type I", allSoj1T1, 15);
        printHistogram("(f) Sojourn time at N1 - Type II", allSoj1T2, 15);
        printHistogram("(g) Sojourn time at N2 station", allSojN2, 15);

        // ── Distribution fitting ──────────────────────────────────────────────
        System.out.println("\n" + "=".repeat(70));
        System.out.println("  DISTRIBUTION FITTING");
        System.out.println("=".repeat(70));
        System.out.println("\n(e) Waiting time distributions:");
        testDistribution("Buffer 1 wait", allWaitB1);
        testDistribution("Buffer 2 wait", allWaitB2);
        System.out.println("\n(f) Sojourn distributions at Node 1:");
        testDistribution("Type-I sojourn at N1", allSoj1T1);
        testDistribution("Type-II sojourn at N1", allSoj1T2);
        System.out.println("\n(g) Sojourn distribution at Node 2 station:");
        testDistribution("Node-2 station sojourn", allSojN2);

        // ── Graphical histograms ──────────────────────────────────────────────
        System.out.println("\n" + "=".repeat(70));
        System.out.println("  GRAPHICAL HISTOGRAMS  (PNG files + Swing window)");
        System.out.println("=".repeat(70));
        showAndSaveHistograms(allWaitB1, allWaitB2, allSoj1T1, allSoj1T2, allSojN2);

        System.out.println("\n" + "=".repeat(70));
        System.out.println("  Simulation complete.");
        System.out.println("=".repeat(70));
    }
}