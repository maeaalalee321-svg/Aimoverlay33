package com.aimoverlay

import kotlin.math.abs
import kotlin.math.atan2
import kotlin.math.cos
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sin
import kotlin.math.sqrt

/** حدود الطاولة الخارجية (حافة الإطار). */
data class TableBox(val l: Float, val t: Float, val r: Float, val b: Float)

/** ملامسة الكرة البيضاء لكرة أخرى. */
data class Contact(
    val ox: Float, val oy: Float,     // مركز الكرة الهدف
    val gx: Float, val gy: Float,     // مركز الكرة البيضاء لحظة التصادم
    val nx: Float, val ny: Float      // اتجاه الكرة الهدف بعد الضربة (وحدة)
)

/**
 * @param lineEnd مسافة نهاية الخط الأبيض الذي ترسمه اللعبة، من مركز الكرة البيضاء
 */
data class Detection(
    val bx: Float,
    val by: Float,
    val angle: Float,
    val radius: Float,
    val lineEnd: Float,
    val table: TableBox,
    val tableW: Float,
    val contact: Contact?
)

/**
 * كاشف يعمل على بكسلات RGB. يحتفظ بحالة بين الإطارات (الطاولة، موضع الكرة، الزاوية)
 * فيصبح أسرع وأثبت: الطاولة تُحسب كل فترة، والكرة تُتتبَّع قرب موضعها السابق.
 */
class Detector {

    /** مقاطع رسم التطبيق السابقة (x1,y1,x2,y2,...) تُستثنى من كشف الكرة. */
    @Volatile
    var exclusions: FloatArray = FloatArray(0)

    /** سبب آخر نتيجة (للتشخيص على الشاشة). */
    @Volatile
    var status: String = ""

    @Volatile
    var dbg: String = ""

    private var table: FloatArray? = null
    private var tableAge = 0
    private var lastW = 0
    private var lastH = 0

    private var fr = 0f
    private var fg = 0f
    private var fb = 0f
    private var fsum = 1f

    private var pBx = -1f
    private var pBy = -1f
    private var pAng = 0f
    private var hasAng = false
    private var pEnd = 0f

    private var pObjAng = 0f
    private var hasObjAng = false
    private var pGd = 0f
    private var hasGd = false

    private var integ = IntArray(0)

    fun reset() {
        table = null
        pBx = -1f
        hasAng = false
    }

    // ------------------------------------------------------------ ألوان

    /** أبيض أو أبيض مُلوَّن بسماوي خفيف (حين يغطي رسم التطبيق خط اللعبة الأبيض). */
    private fun isWhite(c: Int): Boolean {
        val g = (c shr 8) and 255
        val b = c and 255
        val r = (c shr 16) and 255
        return r > 130 && g > 150 && b > 150 && abs(g - b) < 50
    }

    /** أبيض صارم (خطوط اللعبة النقية): لا يلتقط لمعان الكرات ولا أرقامها البيضاء. */
    private fun isWhiteStrict(c: Int): Boolean {
        val g = (c shr 8) and 255
        val b = c and 255
        return g > 205 && b > 205 && abs(g - b) < 40
    }

    /** ألوان رسم التطبيق نفسه (سماوي/ليموني/أرجواني) بعد المزج مع الخلفية. */
    private fun isOverlayColor(c: Int): Boolean {
        val r = (c shr 16) and 255
        val g = (c shr 8) and 255
        val b = c and 255
        if (r < 150 && g > 170 && b > 140 && abs(g - b) < 70) return true
        if (r < 150 && g > 190 && b < 120 && g > r + 80) return true
        if (r > 150 && b > 150 && g < 110) return true
        return false
    }

    private fun isFelt(c: Int): Boolean {
        val r = (c shr 16) and 255
        val g = (c shr 8) and 255
        val b = c and 255
        val s = (r + g + b + 1).toFloat()
        if (s < 0.45f * fsum || s > 2.2f * fsum) return false
        return abs(r / s - fr / fsum) < 0.07f &&
                abs(g / s - fg / fsum) < 0.07f &&
                abs(b / s - fb / fsum) < 0.07f
    }

    /** بكسل كرة ملوّنة: ليس قماشاً ولا أبيض ولا من رسمنا. الكرة السوداء مشمولة. */
    private fun isBallPixel(c: Int): Boolean {
        if (isWhite(c) || isOverlayColor(c)) return false
        val r = (c shr 16) and 255
        val g = (c shr 8) and 255
        val b = c and 255
        val s = (r + g + b + 1).toFloat()
        if (s < 45f) return true
        return !(abs(r / s - fr / fsum) < 0.07f &&
                abs(g / s - fg / fsum) < 0.07f &&
                abs(b / s - fb / fsum) < 0.07f)
    }

    private fun nearExcl(x: Float, y: Float): Boolean {
        val e = exclusions
        var i = 0
        while (i + 3 < e.size) {
            val ax = e[i]; val ay = e[i + 1]
            val vx = e[i + 2] - ax; val vy = e[i + 3] - ay
            val l2 = vx * vx + vy * vy
            var t = if (l2 > 1e-6f) ((x - ax) * vx + (y - ay) * vy) / l2 else 0f
            if (t < 0f) t = 0f else if (t > 1f) t = 1f
            val dx = ax + vx * t - x
            val dy = ay + vy * t - y
            if (dx * dx + dy * dy < 7f) return true
            i += 4
        }
        return false
    }

    // ------------------------------------------------------------ الطاولة

    private fun estimateFelt(px: IntArray, w: Int, h: Int): Boolean {
        val cnt = IntArray(4096)
        val sr = LongArray(4096)
        val sg = LongArray(4096)
        val sb = LongArray(4096)
        var y = (h * 0.3f).toInt()
        val y1 = (h * 0.7f).toInt()
        val x0 = (w * 0.25f).toInt()
        val x1 = (w * 0.75f).toInt()
        while (y < y1) {
            var x = x0
            while (x < x1) {
                val c = px[y * w + x]
                val r = (c shr 16) and 255
                val g = (c shr 8) and 255
                val b = c and 255
                val k = ((r shr 4) shl 8) or ((g shr 4) shl 4) or (b shr 4)
                cnt[k]++; sr[k] += r.toLong(); sg[k] += g.toLong(); sb[k] += b.toLong()
                x += 3
            }
            y += 3
        }
        var bk = 0
        for (k in 1 until 4096) if (cnt[k] > cnt[bk]) bk = k
        if (cnt[bk] < 50) return false
        fr = sr[bk].toFloat() / cnt[bk]
        fg = sg[bk].toFloat() / cnt[bk]
        fb = sb[bk].toFloat() / cnt[bk]
        fsum = fr + fg + fb + 1f
        return true
    }

    private inline fun longestRun(n: Int, gap: Int, test: (Int) -> Boolean): IntArray? {
        var start = -1
        var last = -1
        var bestLen = 0
        var bs = 0
        var be = 0
        for (i in 0 until n) {
            if (test(i)) {
                if (start < 0) start = i
                else if (i - last > gap) {
                    if (last - start > bestLen) { bestLen = last - start; bs = start; be = last }
                    start = i
                }
                last = i
            }
        }
        if (start >= 0 && last - start > bestLen) { bestLen = last - start; bs = start; be = last }
        return if (bestLen > 0) intArrayOf(bs, be) else null
    }

    private fun median(v: MutableList<Int>): Float {
        v.sort()
        return v[v.size / 2].toFloat()
    }

    private fun findTable(px: IntArray, w: Int, h: Int): FloatArray? {
        if (!estimateFelt(px, w, h)) return null
        val lefts = ArrayList<Int>()
        val rights = ArrayList<Int>()
        val gapX = (w * 0.03f).toInt().coerceAtLeast(2)
        var y = (h * 0.35f).toInt()
        val yEnd = (h * 0.75f).toInt()
        while (y < yEnd) {
            val row = y * w
            val run = longestRun(w, gapX) { x -> isFelt(px[row + x]) }
            if (run != null && run[1] - run[0] > w * 0.4f) { lefts.add(run[0]); rights.add(run[1]) }
            y += 3
        }
        if (lefts.size < 8) return null
        val l = median(lefts)
        val r = median(rights)
        val tw = r - l
        val tops = ArrayList<Int>()
        val bots = ArrayList<Int>()
        val gapY = (h * 0.05f).toInt().coerceAtLeast(2)
        var x = (l + tw * 0.15f).toInt()
        val xEnd = (l + tw * 0.85f).toInt()
        while (x < xEnd) {
            val run = longestRun(h, gapY) { yy -> isFelt(px[yy * w + x]) }
            if (run != null && run[1] - run[0] > h * 0.4f) { tops.add(run[0]); bots.add(run[1]) }
            x += 4
        }
        if (tops.size < 8) return null
        // نسبة الطاولة ثابتة تقريباً؛ نصحح الحافة العلوية إن التبست بزخرفة الإطار
        val expectedH = tw * 0.521f
        val bot = median(bots)
        var top = median(tops)
        if (abs((bot - top) - expectedH) > 0.05f * expectedH) top = bot - expectedH
        return floatArrayOf(l, top, r, bot)
    }

    // ------------------------------------------------------------ الكرة البيضاء

    /** تتبّع سريع قرب الموضع السابق. */
    private fun trackBall(px: IntArray, w: Int, h: Int, x0: Float, y0: Float, r: Float): FloatArray? {
        var cx = x0
        var cy = y0
        var cnt = 0
        val rr = r * 1.1f
        repeat(3) {
            var sx = 0f; var sy = 0f; var n = 0
            val ya = max(0, (cy - rr).toInt()); val yb = min(h - 1, (cy + rr).toInt())
            val xa = max(0, (cx - rr).toInt()); val xb = min(w - 1, (cx + rr).toInt())
            for (yy in ya..yb) for (xx in xa..xb) {
                val dx = xx - cx; val dy = yy - cy
                if (dx * dx + dy * dy <= rr * rr && isWhite(px[yy * w + xx])) { sx += xx; sy += yy; n++ }
            }
            cnt = n
            if (n > 0) { cx = sx / n; cy = sy / n }
        }
        val area = Math.PI.toFloat() * rr * rr
        return if (cnt >= 0.35f * area) floatArrayOf(cx, cy) else null
    }

    /** بحث كامل: أكبر كثافة بيضاء بحجم الكرة داخل الطاولة. */
    private fun findCueBall(px: IntArray, w: Int, h: Int, box: FloatArray, r: Float): FloatArray? {
        val k = max(2, (r * 0.9f).toInt())
        val x0 = max(box[0].toInt() + k + 1, k + 1)
        val x1 = min(box[2].toInt() - k - 1, w - k - 2)
        val y0 = max(box[1].toInt() + k + 1, k + 1)
        val y1 = min(box[3].toInt() - k - 1, h - k - 2)
        if (x1 <= x0 || y1 <= y0) return null

        val iw = w + 1
        if (integ.size < iw * (h + 1)) integ = IntArray(iw * (h + 1))
        for (y in 0 until h) {
            var rowSum = 0
            for (x in 0 until w) {
                if (isWhite(px[y * w + x])) rowSum++
                integ[(y + 1) * iw + (x + 1)] = integ[y * iw + (x + 1)] + rowSum
            }
        }
        var best = -1
        var bx = 0
        var by = 0
        var y = y0
        while (y < y1) {
            var x = x0
            while (x < x1) {
                val s = integ[(y + k + 1) * iw + (x + k + 1)] - integ[(y - k) * iw + (x + k + 1)] -
                        integ[(y + k + 1) * iw + (x - k)] + integ[(y - k) * iw + (x - k)]
                if (s > best) { best = s; bx = x; by = y }
                x += 2
            }
            y += 2
        }
        val side = 2 * k + 1
        if (best < side * side * 0.4f) return null
        return trackBall(px, w, h, bx.toFloat(), by.toFloat(), r)
    }

    // ------------------------------------------------------------ خط التصويب

    /** آخر مسافة فيها بكسل أبيض متصل على الشعاع (مع سماح بفجوة 3 بكسل). */
    private fun rayEnd(
        px: IntArray, w: Int, h: Int, cx: Float, cy: Float, a: Float, start: Float, maxD: Float
    ): Float {
        val dx = cos(a)
        val dy = sin(a)
        var d = start
        var miss = 0
        var last = start
        while (d < maxD) {
            val xx = cx + dx * d
            val yy = cy + dy * d
            var hit = false
            for (o in -2..2) {
                val x = (xx - dy * o + 0.5f).toInt()
                val y = (yy + dx * o + 0.5f).toInt()
                if (x in 0 until w && y in 0 until h && isWhite(px[y * w + x])) { hit = true; break }
            }
            if (hit) { miss = 0; last = d } else { miss++; if (miss > 3) break }
            d += 1f
        }
        return last
    }

    private fun angDiff(a: Float, b: Float): Float {
        var d = a - b
        val tp = (2.0 * Math.PI).toFloat()
        while (d > Math.PI) d -= tp
        while (d < -Math.PI) d += tp
        return d
    }

    /**
     * تحسين اتجاه خط التصويب بملاءمة خط مستقيم (PCA) لبكسلاته البيضاء؛ أدق بكثير من اختيار شعاع.
     * يعيد [cos, sin, نقطة_على_الخط_x, y] أو null.
     */
    private fun fitAimLine(
        px: IntArray, w: Int, h: Int, cx: Float, cy: Float, ang: Float, r: Float, end: Float
    ): FloatArray? {
        val d0 = 1.7f * r
        val d1 = end - 0.6f * r
        if (d1 - d0 < 2f * r) return null
        return fitLine(px, w, h, cx, cy, ang, d0, d1, 2.6f, 12, 0.06f, false)
    }

    /** ملاءمة خط مستقيم (PCA) لبكسلات بيضاء ضمن شريط حول شعاع. يرجع [cos, sin, نقطة x, y] أو null. */
    private fun fitLine(
        px: IntArray, w: Int, h: Int, cx: Float, cy: Float, ang: Float,
        d0: Float, d1: Float, band: Float, minN: Int, maxDev: Float, strict: Boolean
    ): FloatArray? {
        val ux = cos(ang); val uy = sin(ang)
        var n = 0
        var mx = 0.0; var my = 0.0
        val xs = ArrayList<Int>(); val ys = ArrayList<Int>()
        val xa = max(0, (min(cx, cx + ux * d1) - 4f).toInt()); val xb = min(w - 1, (max(cx, cx + ux * d1) + 4f).toInt())
        val ya = max(0, (min(cy, cy + uy * d1) - 4f).toInt()); val yb = min(h - 1, (max(cy, cy + uy * d1) + 4f).toInt())
        for (y in ya..yb) for (x in xa..xb) {
            val vx = x - cx; val vy = y - cy
            val al = vx * ux + vy * uy
            if (al < d0 || al > d1) continue
            if (abs(vx * uy - vy * ux) > band) continue
            val c = px[y * w + x]
            if (!(if (strict) isWhiteStrict(c) else isWhite(c))) continue
            xs.add(x); ys.add(y); mx += x; my += y; n++
        }
        if (n < minN) return null
        mx /= n; my /= n
        var sxx = 0.0; var syy = 0.0; var sxy = 0.0
        for (i in 0 until n) {
            val dx = xs[i] - mx; val dy = ys[i] - my
            sxx += dx * dx; syy += dy * dy; sxy += dx * dy
        }
        var th = (0.5 * atan2(2 * sxy, sxx - syy)).toFloat()
        if (cos(th) * ux + sin(th) * uy < 0f) th += Math.PI.toFloat()
        if (abs(angDiff(th, ang)) > maxDev) return null
        val tx = cos(th); val ty = sin(th)
        val t = (cx - mx.toFloat()) * tx + (cy - my.toFloat()) * ty
        return floatArrayOf(tx, ty, mx.toFloat() + tx * t, my.toFloat() + ty * t)
    }

    // ------------------------------------------------------------ الكرة الهدف

    private fun findContact(
        px: IntArray, w: Int, h: Int, tb: FloatArray, r: Float,
        gx: Float, gy: Float, bx: Float, by: Float, dx: Float, dy: Float
    ): Contact? {
        val ya = max(max(0, (gy - 3f * r).toInt()), tb[1].toInt())
        val yb = min(min(h - 1, (gy + 3f * r).toInt()), tb[3].toInt())
        val xa = max(max(0, (gx - 3f * r).toInt()), tb[0].toInt())
        val xb = min(min(w - 1, (gx + 3f * r).toInt()), tb[2].toInt())
        var sx = 0f; var sy = 0f; var n = 0
        for (y in ya..yb) for (x in xa..xb) {
            val ddx = x - gx; val ddy = y - gy
            val d2 = ddx * ddx + ddy * ddy
            if (d2 >= (1.4f * r) * (1.4f * r) && d2 <= 9f * r * r &&
                isBallPixel(px[y * w + x]) && !nearExcl(x.toFloat(), y.toFloat())) {
                sx += x; sy += y; n++
            }
        }
        val area = Math.PI.toFloat() * r * r
        if (n < 0.3f * area) return null
        var cx = sx / n
        var cy = sy / n
        var cnt = 0
        repeat(4) {
            var ax = 0f; var ay = 0f; var k = 0
            val rr = r * 1.15f
            val y0 = max(max(0, (cy - rr).toInt()), tb[1].toInt())
            val y1 = min(min(h - 1, (cy + rr).toInt()), tb[3].toInt())
            val x0 = max(max(0, (cx - rr).toInt()), tb[0].toInt())
            val x1 = min(min(w - 1, (cx + rr).toInt()), tb[2].toInt())
            for (y in y0..y1) for (x in x0..x1) {
                val ddx = x - cx; val ddy = y - cy
                val gdx = x - gx; val gdy = y - gy
                if (ddx * ddx + ddy * ddy <= rr * rr &&
                    gdx * gdx + gdy * gdy >= 1.69f * r * r &&          // حلقة الكرة الشبحية البيضاء تُنتج بكسلات رمادية كاذبة
                    isBallPixel(px[y * w + x]) && !nearExcl(x.toFloat(), y.toFloat())) { ax += x; ay += y; k++ }
            }
            cnt = k
            if (k >= 5) { cx = ax / k; cy = ay / k }
        }
        if (cnt < 0.26f * area) return null

        val proj = (cx - bx) * dx + (cy - by) * dy
        val perp = abs(-(cx - bx) * dy + (cy - by) * dx)
        if (perp >= 2f * r) return null
        val t = proj - sqrt(4f * r * r - perp * perp)
        if (t <= 0f) return null
        val g2x = bx + dx * t
        val g2y = by + dy * t
        return Contact(cx, cy, g2x, g2y, (cx - g2x) / (2f * r), (cy - g2y) / (2f * r))
    }

    /**
     * اتجاه الكرة الهدف بدقة: اللعبة نفسها ترسم خطاً أبيض قصيراً يمرّ بمركز الكرة الهدف
     * ويمتد خارجها. نجمع بكسلاته ونحسب محوره الرئيسي (PCA)، وهو أدق بكثير من مركزين متقاربين.
     * يرجع [dx, dy, ox, oy] أو null.
     */
    private fun refineObjectDir(
        px: IntArray, w: Int, h: Int, r: Float, cx: Float, cy: Float, n0x: Float, n0y: Float
    ): FloatArray? {
        val ya = max(0, (cy - 5.5f * r).toInt()); val yb = min(h - 1, (cy + 5.5f * r).toInt())
        val xa = max(0, (cx - 5.5f * r).toInt()); val xb = min(w - 1, (cx + 5.5f * r).toInt())
        var sx = 0.0; var sy = 0.0; var n = 0
        for (y in ya..yb) for (x in xa..xb) {
            val vx = x - cx; val vy = y - cy
            val along = vx * n0x + vy * n0y
            if (along < 1.2f * r || along > 4.9f * r) continue
            val perp = -vx * n0y + vy * n0x
            if (abs(perp) > 0.7f * along) continue
            if (!isWhite(px[y * w + x])) continue
            sx += x; sy += y; n++
        }
        if (n < 10) return null
        val mx = sx / n
        val my = sy / n
        var sxx = 0.0; var sxy = 0.0; var syy = 0.0
        for (y in ya..yb) for (x in xa..xb) {
            val vx = x - cx; val vy = y - cy
            val along = vx * n0x + vy * n0y
            if (along < 1.2f * r || along > 4.9f * r) continue
            val perp = -vx * n0y + vy * n0x
            if (abs(perp) > 0.7f * along) continue
            if (!isWhite(px[y * w + x])) continue
            val ddx = x - mx; val ddy = y - my
            sxx += ddx * ddx; sxy += ddx * ddy; syy += ddy * ddy
        }
        val half = (sxx + syy) / 2.0
        val dif = sqrt(((sxx - syy) / 2.0) * ((sxx - syy) / 2.0) + sxy * sxy)
        val l1 = half + dif
        val l2 = half - dif
        if (l1 < 4.0 * l2 + 1e-3) return null                 // ليست خطاً مستقيماً
        val a = 0.5 * atan2(2.0 * sxy, sxx - syy)
        var dx = cos(a).toFloat()
        var dy = sin(a).toFloat()
        if (dx * n0x + dy * n0y < 0f) { dx = -dx; dy = -dy }
        if (abs(angDiff(atan2(dy, dx), atan2(n0y, n0x))) > 0.9f) return null
        val t = (cx - mx.toFloat()) * dx + (cy - my.toFloat()) * dy
        return floatArrayOf(dx, dy, mx.toFloat() + dx * t, my.toFloat() + dy * t)
    }

    /**
     * اتجاه الكرة الهدف من الخط الأبيض القصير الذي ترسمه اللعبة من مركزها.
     * نبحث بأشعة (±40°) عن أطول امتداد أبيض متصل يبدأ من حافة الكرة، ثم نحسّنه بملاءمة خط.
     * أمتن من PCA على منطقة كاملة: لا تفسده أرقام الكرات البيضاء المجاورة.
     * يرجع [dx, dy, ox, oy] أو null.
     */
    private fun objectRay(
        px: IntArray, w: Int, h: Int, r: Float, cx: Float, cy: Float, n0x: Float, n0y: Float
    ): FloatArray? {
        val base = atan2(n0y, n0x)
        val d0 = 1.15f * r
        val dEnd = 5.2f * r
        val lens = FloatArray(101)
        var bestLen = 0f
        for (i in -50..50) {
            val a = base + i * 0.017453f
            val dx = cos(a); val dy = sin(a)
            var d = d0
            var miss = 0
            var last = -1f
            while (d < dEnd) {
                val xx = cx + dx * d; val yy = cy + dy * d
                var hit = false
                for (o in -1..1) {
                    val x = (xx - dy * o + 0.5f).toInt()
                    val y = (yy + dx * o + 0.5f).toInt()
                    if (x in 0 until w && y in 0 until h && isWhiteStrict(px[y * w + x])) { hit = true; break }
                }
                if (hit) { miss = 0; last = d } else { miss++; if (miss > 2) break }
                d += 1f
            }
            val len = if (last < 0f) 0f else last - d0
            lens[i + 50] = len
            if (len > bestLen) bestLen = len
        }
  
