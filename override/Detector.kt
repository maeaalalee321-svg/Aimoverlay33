
    /** بحث أحادي البعد عن الحلقة على امتداد خط التصويب (الضربات البعيدة). يرجع المسافة أو -1. */
    private fun findRingRay(
        px: IntArray, w: Int, h: Int, cx: Float, cy: Float, ux: Float, uy: Float, r: Float, tMax: Float
    ): Float {
        val ns = 48
        var best = -1000
        val ts = ArrayList<Float>(); val scs = ArrayList<Int>()
        var t = 1.0f * r
        while (t <= tMax) {
            val gx = cx + ux * t; val gy = cy + uy * t
            val qc = ringCount(px, w, h, gx, gy, r, 8, cx, cy, r)
            if (qc[0] < 3 || qc[1] < 0.5f * qc[0]) { t += 1.0f; continue }
            val rc = ringCount(px, w, h, gx, gy, r, ns, cx, cy, r)
            if (rc[0] >= 22 && rc[1] >= 0.68f * rc[0] && ringHollow(px, w, h, gx, gy, cx, cy, r)) {
                val sc = rc[1] * 2 - rc[0]
                if (sc > best) best = sc
                ts.add(t); scs.add(sc)
            }
            t += 1.0f
        }
        if (best < 0) return -1f
        var sum = 0f; var n = 0
        for (i in scs.indices) if (scs[i] >= best - 3) { sum += ts[i]; n++ }
        return sum / n
    }

    private fun whiteAround(px: IntArray, w: Int, h: Int, x: Float, y: Float, nx: Float, ny: Float): Boolean {
        for (o in -1..1) {
            val xx = (x - ny * o + 0.5f).toInt()
            val yy = (y + nx * o + 0.5f).toInt()
            if (xx in 0 until w && yy in 0 until h && isWhiteStrict(px[yy * w + xx])) return true
        }
        return false
    }

    /**
     * الخط الأبيض الذي ترسمه اللعبة من مركز الكرة الهدف بمحاذاة اتجاه حركتها. يبدأ على بعد 2r من
     * مركز الحلقة، وبين الحلقة والكرة لا يوجد أبيض (بخلاف المماس وخط التصويب). نبحث عن أطول امتداد
     * أبيض ثم نلاءمه بـ PCA. يرجع [nx, ny, ox, oy, طول] أو null.
     */
    private fun findObjectLine(
        px: IntArray, w: Int, h: Int, r: Float, gx: Float, gy: Float, ux: Float, uy: Float
    ): FloatArray? {
        val lens = FloatArray(360)
        var bestLen = 0f
        for (k in 0 until 360) {
            val a = k * Math.PI.toFloat() / 180f
            val dx = cos(a); val dy = sin(a)
            if (dx * ux + dy * uy < 0.02f) continue
            var last = -1f
            var miss = 0
            var first = -1f
            var t = 2.0f * r
            while (t <= 9f * r) {
                if (whiteAround(px, w, h, gx + dx * t, gy + dy * t, dx, dy)) {
                    if (first < 0f) first = t
                    last = t; miss = 0
                } else {
                    if (first < 0f && t > 2.8f * r) break
                    miss++
                    if (first >= 0f && miss > 3) break
                }
                t += 0.75f
            }
            if (first < 0f || first > 2.8f * r) continue
            val len = last - 2.0f * r
            lens[k] = len
            if (len > bestLen) bestLen = len
        }
        if (bestLen < 1.6f * r) return null
        // متوسط الزوايا القريبة من الأفضل
        var sx = 0.0; var sy = 0.0
        for (k in 0 until 360) if (lens[k] >= 0.9f * bestLen) {
            val a = k * Math.PI / 180.0
            sx += cos(a); sy += sin(a)
        }
        var cur = atan2(sy, sx).toFloat()
        // ملاءمة PCA لبكسلات الخط
        var mx = gx; var my = gy
        var res: FloatArray? = null
        for (iter in 0 until 3) {
            val dx = cos(cur); val dy = sin(cur)
            var n = 0
            val xs = ArrayList<Int>(); val ys = ArrayList<Int>()
            val x0 = max(0, (gx - 10f * r).toInt()); val x1 = min(w - 1, (gx + 10f * r).toInt())
            val y0 = max(0, (gy - 10f * r).toInt()); val y1 = min(h - 1, (gy + 10f * r).toInt())
            val endD = 2.0f * r + bestLen + 1.5f
            for (y in y0..y1) for (x in x0..x1) {
                val vx = x - gx; val vy = y - gy
                val al = vx * dx + vy * dy
                if (al < 1.9f * r || al > endD) continue
                if (abs(vx * dy - vy * dx) > 2.6f) continue
                if (!isWhiteStrict(px[y * w + x])) continue
                xs.add(x); ys.add(y); n++
            }
            if (n < 10) return null
            var sx2 = 0.0; var sy2 = 0.0
            for (i in 0 until n) { sx2 += xs[i]; sy2 += ys[i] }
            val mxx = sx2 / n; val myy = sy2 / n
            var sxx = 0.0; var syy = 0.0; var sxy = 0.0
            for (i in 0 until n) {
                val ddx = xs[i] - mxx; val ddy = ys[i] - myy
                sxx += ddx * ddx; syy += ddy * ddy; sxy += ddx * ddy
            }
            var th = (0.5 * atan2(2.0 * sxy, sxx - syy)).toFloat()
            if (cos(th) * dx + sin(th) * dy < 0f) th += Math.PI.toFloat()
            if (abs(angDiff(th, cur)) > 0.2f) return null
            cur = atan2(sin(th), cos(th))
            mx = mxx.toFloat(); my = myy.toFloat()
        }
        val nx = cos(cur); val ny = sin(cur)
        // مركز الكرة الهدف: على الخط، على بعد 2r من مسقط مركز الحلقة
        val tg = (gx - mx) * nx + (gy - my) * ny
        val px0 = mx + nx * tg; val py0 = my + ny * tg
        res = floatArrayOf(nx, ny, px0 + 2f * r * nx, py0 + 2f * r * ny, bestLen)
        return res
    }

    // ------------------------------------------------------------ الواجهة

    fun detect(px: IntArray, w: Int, h: Int): Detection? {
        if (w != lastW || h != lastH) { reset(); lastW = w; lastH = h }

        tableAge++
        if (table == null || tableAge > 40) {
            val t = findTable(px, w, h)
            if (t != null) {
                val old = table
                val same = old != null && abs(old[0] - t[0]) < 3f && abs(old[1] - t[1]) < 3f &&
                        abs(old[2] - t[2]) < 3f && abs(old[3] - t[3]) < 3f
                if (!same) table = t
                tableAge = 0
            } else if (table == null) { status = "لا طاولة"; return null } else tableAge = 30
        }
        val tb = table ?: return null
        val tw = tb[2] - tb[0]
        if (tw < w * 0.4f) { table = null; status = "لا طاولة"; return null }
        val r = tw * 0.0136f

        var ball = if (pBx >= 0f) trackBall(px, w, h, pBx, pBy, r) else null
        if (ball == null) ball = findCueBall(px, w, h, tb, r)
        if (ball == null) { pBx = -1f; hasAng = false; status = "لا كرة بيضاء"; return null }
        val cx = ball[0]
        val cy = ball[1]
        pBx = cx; pBy = cy

        val q = when (smooth) { 0 -> 1f; 1 -> 0.75f; 2 -> 0.55f; 3 -> 0.4f; else -> 0.25f }
        val start = r * 1.5f
        // ضربة قريبة: الحلقة ملاصقة للكرة البيضاء فلا يظهر خط تصويب
        val near = findRingNear(px, w, h, cx, cy, r)
        var ang: Float
        var end: Float
        var lcx = cx
        var lcy = cy
        if (near != null) {
            ang = atan2(near[1] - cy, near[0] - cx)
            end = hypot(near[0] - cx, near[1] - cy) - r
        } else {
            val coarseMax = min(tw * 0.2f, 170f)
            val step = (2.0 * Math.PI / 180.0).toFloat()
            var ca = 0f
            var bestC = -1f
            for (i in 0 until 180) {
                val a2 = i * step
                val e = rayEnd(px, w, h, cx, cy, a2, start, coarseMax)
                if (e > bestC) { bestC = e; ca = a2 }
            }
            if (bestC - start < r * 1.5f) {
                hasAng = false; hasGd = false; pBx = -1f
                status = "لا خط تصويب (كرة ${cx.toInt()},${cy.toInt()} طول ${((bestC - start) / r * 10).toInt() / 10f}R)"
                return null
            }
            if (hasAng) {
                val ep = rayEnd(px, w, h, cx, cy, pAng, start, coarseMax)
                if (ep - start >= 0.85f * (bestC - start)) ca = pAng
            }
            val maxD = tw * 0.9f
            val fine = 17
            val ends = FloatArray(fine)
            val fstep = (0.25 * Math.PI / 180.0).toFloat()
            var bestE = -1f
            for (k in 0 until fine) {
                val a2 = ca + (k - fine / 2) * fstep
                ends[k] = rayEnd(px, w, h, cx, cy, a2, start, maxD)
                if (ends[k] > bestE) bestE = ends[k]
            }
            if (bestE - start < r * 2f) {
                hasAng = false; hasGd = false; pBx = -1f
                status = "خط قصير (كرة ${cx.toInt()},${cy.toInt()} طول ${((bestE - start) / r * 10).toInt() / 10f}R)"
                return null
            }
            var sx = 0.0
            var sy = 0.0
            for (k in 0 until fine) {
                if (ends[k] >= bestE - 2f) {
                    val a2 = ca + (k - fine / 2) * fstep
                    sx += cos(a2); sy += sin(a2)
                }
            }
            ang = atan2(sy, sx).toFloat()
            end = bestE
            val fit = fitAimLine(px, w, h, cx, cy, ang, r, end)
            if (fit != null) {
                ang = atan2(fit[1], fit[0])
                lcx = fit[2]; lcy = fit[3]
            }
        }
        if (hasAng) {
            val dd = angDiff(ang, pAng)
            val ad = abs(dd)
            ang = when {
                ad < 0.0045f -> pAng                  // اهتزاز أقل من 0.26 درجة: نثبّت
                ad < 0.03f -> pAng + 0.3f * q * dd
                ad < 0.12f -> pAng + 0.6f * q * dd
                else -> ang
            }
            if (abs(end - pEnd) < 6f) end = 0.5f * (end + pEnd)
        }
        pAng = ang; pEnd = end; hasAng = true

        val ux = cos(ang)
        val uy = sin(ang)
        status = ""
        // مركز الكرة الشبحية من الحلقة (لا من نهاية الخط)
        var gd: Float
        var ringOk = true
        if (near != null) {
            gd = hypot(near[0] - cx, near[1] - cy)
        } else {
            val rg = findRingRay(px, w, h, lcx, lcy, ux, uy, r, min(end + 4f * r, tw * 0.95f))
            if (rg > 0f) gd = rg else { gd = end + r; ringOk = false }
        }
        if (hasGd && abs(gd - pGd) < 2f) gd = pGd + 0.5f * q * (gd - pGd)
        pGd = gd; hasGd = true
        end = gd - r
        pEnd = end
        val gx = lcx + ux * gd
        val gy = lcy + uy * gd
        var contact: Contact? = null
        val ol = if (ringOk) findObjectLine(px, w, h, r, gx, gy, ux, uy) else null
        val tick = if (ol == null) findTick(px, w, h, r, gx, gy, ux, uy) else null
        val tpl = if (ol == null) templateContact(px, w, h, tb, r, gx, gy, ux, uy) else null
        if (ol != null) {
            contact = Contact(ol[2], ol[3], gx, gy, ol[0], ol[1])
            status = if (near != null) "ملامسة ✓ (خط الهدف، قريبة)" else "ملامسة ✓ (خط الهدف)"
        } else if (tick != null && (tpl == null || abs(angDiff(atan2(tick[1], tick[0]), atan2(tpl[1], tpl[0]))) < 0.35f)) {
            contact = Contact(tick[2], tick[3], gx, gy, tick[0], tick[1])
            status = "ملامسة ✓ (خط اللعبة)"
        } else if (tpl != null) {
            contact = Contact(gx + 2f * r * tpl[0], gy + 2f * r * tpl[1], gx, gy, tpl[0], tpl[1])
            status = "ملامسة ~ (قالب ${(tpl[2] * 100).toInt()})"
        }
        if (contact != null) {
            // تنعيم اتجاه الكرة الهدف (يقلّل اهتزاز نهاية الخط عند الحافة)
            var oa = atan2(contact.ny, contact.nx)
            if (hasObjAng) {
                val dd = angDiff(oa, pObjAng)
                oa = when {
                    abs(dd) < 0.006f -> pObjAng
                    abs(dd) < 0.09f -> pObjAng + 0.3f * q * dd
                    else -> oa
                }
            }
            pObjAng = oa; hasObjAng = true
            contact = Contact(contact.ox, contact.oy, contact.gx, contact.gy, cos(oa), sin(oa))
        } else {
            hasObjAng = false
            status = "خط تصويب بلا كرة هدف"
        }
        return Detection(lcx, lcy, ang, r, end, TableBox(tb[0], tb[1], tb[2], tb[3]), tw, contact)
    }
}
