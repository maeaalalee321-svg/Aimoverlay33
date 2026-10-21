package com.aimoverlay

import android.Manifest
import android.app.Activity
import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.content.pm.ServiceInfo
import android.content.res.Configuration
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Path as GPath
import android.graphics.PixelFormat
import android.graphics.drawable.GradientDrawable
import android.hardware.display.DisplayManager
import android.hardware.display.VirtualDisplay
import android.media.ImageReader
import android.media.projection.MediaProjection
import android.media.projection.MediaProjectionManager
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.HandlerThread
import android.os.IBinder
import android.os.Looper
import android.provider.Settings
import android.util.DisplayMetrics
import android.view.Gravity
import android.view.MotionEvent
import android.view.View
import android.view.WindowManager
import android.widget.Button
import android.widget.CheckBox
import android.widget.LinearLayout
import android.widget.SeekBar
import android.widget.TextView
import android.widget.Toast
import androidx.activity.ComponentActivity
import androidx.activity.result.contract.ActivityResultContracts
import kotlin.math.abs
import kotlin.math.cos
import kotlin.math.hypot
import kotlin.math.sin

// ===== Trajectory.kt =====
/**
 * خطة الرسم:
 *  cue      مسار الكرة البيضاء (مع الارتداد إن لم تلامس كرة)
 *  ring     مركز الدائرة التي تُرسم في نهاية المسار (الكرة الشبحية أو نهاية الارتداد)
 *  deflect  اتجاه الكرة البيضاء بعد الاصطدام بكرة
 *  obj      مسار الكرة الهدف
 *  potted   هل الكرة الهدف تدخل جيباً
 */
class Plan(
    val cue: List<FloatArray>,
    val ring: FloatArray,
    val deflect: List<FloatArray>?,
    val obj: List<FloatArray>?,
    val potted: Boolean,
    val radius: Float
)

object Trajectory {

    fun compute(d: Detection, inset: Float, maxBounces: Int, showObject: Boolean): Plan {
        val r = d.radius
        val raw = d.table
        // مركز الكرة يرتد على بعد (نصف قطر + عرض الحافة المائلة ≈ 1.5 نصف قطر) من حافة الإطار
        val m = 2.5f * r + inset
        val box = TableBox(raw.l + m, raw.t + m, raw.r - m, raw.b - m)
        val ux = cos(d.angle)
        val uy = sin(d.angle)

        // مسافة أول حافة على الشعاع
        val tx = when {
            ux > 1e-6f -> (box.r - d.bx) / ux
            ux < -1e-6f -> (box.l - d.bx) / ux
            else -> Float.MAX_VALUE
        }
        val ty = when {
            uy > 1e-6f -> (box.b - d.by) / uy
            uy < -1e-6f -> (box.t - d.by) / uy
            else -> Float.MAX_VALUE
        }
        val wallT = minOf(tx, ty)
        val ghostDist = d.lineEnd + r                       // مركز الكرة الشبحية

        // ملامسة كرة: إما اكتُشفت الكرة الهدف، أو انتهى خط اللعبة قبل الحافة بوضوح
        val c = d.contact
        val ended = d.lineEnd > r * 0.5f && ghostDist < wallT - 2f * r
        if (c != null || ended) {
            val gx = if (c != null) c.gx else d.bx + ux * ghostDist
            val gy = if (c != null) c.gy else d.by + uy * ghostDist
            val cue = listOf(floatArrayOf(d.bx, d.by), floatArrayOf(gx, gy))
            if (!showObject || c == null)
                return Plan(cue, floatArrayOf(gx, gy), null, null, false, r)

            // اتجاه الكرة البيضاء بعد الاصطدام: المركبة العمودية على خط التماس
            val dot = ux * c.nx + uy * c.ny
            var px = ux - c.nx * dot
            var py = uy - c.ny * dot
            val tl = hypot(px, py)
            var deflect: List<FloatArray>? = null
            if (tl > 0.15f) {
                px /= tl; py /= tl
                val len = r * (3f + 5f * tl)
                deflect = listOf(floatArrayOf(gx, gy), floatArrayOf(gx + px * len, gy + py * len))
            }
            val (path, potted) = objectPath(c.ox, c.oy, c.nx, c.ny, box, raw, r, maxBounces)
            return Plan(cue, floatArrayOf(gx, gy), deflect, path, potted, r)
        }
        val pts = bouncePath(d.bx, d.by, ux, uy, box, maxBounces, d.tableW * 6f)
        return Plan(pts, pts.last(), null, null, false, r)
    }

    private fun bouncePath(
        sx: Float, sy: Float, ux: Float, uy: Float,
        box: TableBox, maxBounces: Int, maxTotal: Float
    ): List<FloatArray> {
        var x = sx
        var y = sy
        var dx = ux
        var dy = uy
        val pts = ArrayList<FloatArray>()
        pts.add(floatArrayOf(x, y))
        var travelled = 0f
        var bounces = 0
        while (true) {
            val tx = when {
                dx > 1e-6f -> (box.r - x) / dx
                dx < -1e-6f -> (box.l - x) / dx
                else -> Float.MAX_VALUE
            }
            val ty = when {
                dy > 1e-6f -> (box.b - y) / dy
                dy < -1e-6f -> (box.t - y) / dy
                else -> Float.MAX_VALUE
            }
            var t = minOf(tx, ty)
            if (t < 0f) t = 0f
            if (travelled + t > maxTotal) {
                val rest = maxTotal - travelled
                pts.add(floatArrayOf(x + dx * rest, y + dy * rest))
                break
            }
            x += dx * t
            y += dy * t
            travelled += t
            pts.add(floatArrayOf(x, y))
            if (bounces == maxBounces) break
            if (tx <= ty) dx = -dx else dy = -dy
            bounces++
        }
        return pts
    }

    /** مسار الكرة الهدف: يرتد عن الحواف maxBounces مرة، وينتهي إن دخل جيباً في أي مقطع. */
    private fun objectPath(
        ox: Float, oy: Float, nx0: Float, ny0: Float,
        box: TableBox, raw: TableBox, r: Float, maxBounces: Int
    ): Pair<List<FloatArray>, Boolean> {
        val midX = (raw.l + raw.r) / 2f
        val pockets = arrayOf(
            floatArrayOf(raw.l, raw.t, 2.3f * r), floatArrayOf(raw.r, raw.t, 2.3f * r),
            floatArrayOf(raw.l, raw.b, 2.3f * r), floatArrayOf(raw.r, raw.b, 2.3f * r),
            floatArrayOf(midX, raw.t, 1.8f * r), floatArrayOf(midX, raw.b, 1.8f * r)
        )
        var x = ox
        var y = oy
        var nx = nx0
        var ny = ny0
        val pts = ArrayList<FloatArray>()
        var bounces = 0
        var first = true
        while (true) {
            val tx = when {
                nx > 1e-6f -> (box.r - x) / nx
                nx < -1e-6f -> (box.l - x) / nx
                else -> Float.MAX_VALUE
            }
            val ty = when {
                ny > 1e-6f -> (box.b - y) / ny
                ny < -1e-6f -> (box.t - y) / ny
                else -> Float.MAX_VALUE
            }
            val tWall = maxOf(0f, minOf(tx, ty))

            var bestT = Float.MAX_VALUE
            var bx = 0f
            var by = 0f
            for (p in pockets) {
                val vx = p[0] - x
                val vy = p[1] - y
                val along = vx * nx + vy * ny
                val perp = abs(vx * ny - vy * nx)
                if (along > 0f && perp < p[2] && along < bestT) { bestT = along; bx = p[0]; by = p[1] }
            }

            if (first) {
                // نبدأ الرسم بعد نهاية الخط الأبيض القصير الذي ترسمه اللعبة، فلا نغطّيه ويبقى مرئياً للكاشف
                val off = minOf(4.4f * r, 0.9f * minOf(tWall, if (bestT < Float.MAX_VALUE) bestT else tWall))
                pts.add(floatArrayOf(x + nx * off, y + ny * off))
                first = false
            }
            if (bestT < tWall + 3f * r) {
                pts.add(floatArrayOf(bx, by))
                return Pair(pts, true)
            }
            val ex = x + nx * tWall
            val ey = y + ny * tWall
            pts.add(floatArrayOf(ex, ey))
            if (bounces >= maxBounces) break
            if (tx <= ty) nx = -nx else ny = -ny
            x = ex; y = ey
            bounces++
        }
        return Pair(pts, false)
    }
}

// ===== AimOverlayView.kt =====
/** طبقة شفافة ترسم الخطة فوق اللعبة. الإحداثيات بوحدة لقطة الشاشة المصغّرة. */
class AimOverlayView(context: Context) : View(context) {

    private var plan: Plan? = null
    private var showCue = false
    private var status = ""
    private var showStatus = false
    private val statusPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(255, 220, 0)
        textSize = 30f
        setShadowLayer(4f, 0f, 0f, Color.BLACK)
    }

    fun setStatus(s: String, show: Boolean) {
        if (s != status || show != showStatus) {
            status = s; showStatus = show
            invalidate()
        }
    }
    private var sx = 1f
    private var sy = 1f

    // ألوان لا تلتبس على الكاشف: سماوي للكرة البيضاء، وأخضر ليموني للكرة الهدف
    private fun stroke(color: Int, w: Float) = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE
        strokeWidth = w
        strokeCap = Paint.Cap.ROUND
        strokeJoin = Paint.Join.ROUND
        this.color = color
    }

    private val cyan = Color.argb(175, 0, 255, 255)
    private val lime = Color.argb(175, 60, 255, 0)
    private val cueLine = stroke(cyan, 6f)
    private val objLine = stroke(lime, 6f)
    private val thin = stroke(Color.argb(150, 0, 255, 255), 3f)
    private val shadow = stroke(Color.argb(0, 0, 0, 0), 1f)
    private val ringCyan = stroke(cyan, 5f)
    private val ringLime = stroke(lime, 5f)
    private val fillLime = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL; color = lime }
    private val bounceDot = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.FILL
        color = Color.argb(200, 255, 0, 255)
    }

    fun update(p: Plan, capW: Int, capH: Int, cue: Boolean) {
        plan = p
        showCue = cue
        sx = width.toFloat() / capW
        sy = height.toFloat() / capH
        invalidate()
    }

    fun clear() {
        if (plan != null) {
            plan = null
            invalidate()
        }
    }

    private fun path(pts: List<FloatArray>): GPath {
        val g = GPath()
        g.moveTo(pts[0][0] * sx, pts[0][1] * sy)
        for (i in 1 until pts.size) g.lineTo(pts[i][0] * sx, pts[i][1] * sy)
        return g
    }

    override fun onDraw(canvas: Canvas) {
        if (showStatus && status.isNotEmpty()) canvas.drawText(status, 24f, 60f, statusPaint)
        val p = plan ?: return
        val rad = p.radius * sx

        if (showCue) {
            if (p.cue.size >= 2) {
                val g = path(p.cue)
                canvas.drawPath(g, cueLine)
                for (i in 1 until p.cue.size - 1) canvas.drawCircle(p.cue[i][0] * sx, p.cue[i][1] * sy, 7f, bounceDot)
            }
            canvas.drawCircle(p.ring[0] * sx, p.ring[1] * sy, rad, ringCyan)
            p.deflect?.let { canvas.drawPath(path(it), thin) }
        }
        p.obj?.let {
            val g = path(it)
            canvas.drawPath(g, objLine)
            val e = it.last()
            if (p.potted) canvas.drawCircle(e[0] * sx, e[1] * sy, rad * 0.8f, fillLime)
            else canvas.drawCircle(e[0] * sx, e[1] * sy, rad, ringLime)
        }
    }
}

// ===== OverlayService.kt =====
class OverlayService : Service() {

    companion object {
        const val ACTION_STOP = "com.aimoverlay.STOP"
        const val EXTRA_CODE = "code"
        const val EXTRA_DATA = "data"
        private const val CHANNEL = "aim"
        private const val SCALE = 2          // نصغّر اللقطة للنصف لسرعة المعالجة
        private const val MIN_INTERVAL_MS = 25L
    }

    private var projection: MediaProjection? = null
    private var display: VirtualDisplay? = null
    private var reader: ImageReader? = null
    private var overlay: AimOverlayView? = null
    private lateinit var wm: WindowManager
    private val detector = Detector()
    private lateinit var thread: HandlerThread
    private lateinit var bg: Handler
    private val main = Handler(Looper.getMainLooper())
    private var lastRun = 0L
    private var lastGood = 0L
    private var capW = 0
    private var capH = 0
    private var px = IntArray(0)
    @Volatile
    private var enabled = true
    private var bubble: TextView? = null

    override fun onBind(intent: Intent?): IBinder? = null

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        if (intent?.action == ACTION_STOP) {
            stopSelf()
            return START_NOT_STICKY
        }
        if (projection != null) return START_NOT_STICKY

        startAsForeground()

        val code = intent?.getIntExtra(EXTRA_CODE, 0) ?: 0
        val data: Intent? = if (Build.VERSION.SDK_INT >= 33)
            intent?.getParcelableExtra(EXTRA_DATA, Intent::class.java)
        else
            @Suppress("DEPRECATION") intent?.getParcelableExtra(EXTRA_DATA)
        if (data == null) {
            stopSelf()
            return START_NOT_STICKY
        }

        thread = HandlerThread("aim-detect").also { it.start() }
        bg = Handler(thread.looper)

        val mpm = getSystemService(Context.MEDIA_PROJECTION_SERVICE) as MediaProjectionManager
        projection = mpm.getMediaProjection(code, data).also {
            // أندرويد 14 يشترط تسجيل callback قبل إنشاء الشاشة الافتراضية
            it.registerCallback(object : MediaProjection.Callback() {
                override fun onStop() {
                    main.post { stopSelf() }
                }
            }, main)
        }

        wm = getSystemService(Context.WINDOW_SERVICE) as WindowManager
        addOverlay()
        addBubble()
        setupCapture()
        return START_NOT_STICKY
    }

    private fun startAsForeground() {
        val nm = getSystemService(NotificationManager::class.java)
        nm.createNotificationChannel(
            NotificationChannel(CHANNEL, "خط التصويب", NotificationManager.IMPORTANCE_LOW)
        )
        val stop = PendingIntent.getService(
            this, 0,
            Intent(this, OverlayService::class.java).setAction(ACTION_STOP),
            PendingIntent.FLAG_IMMUTABLE or PendingIntent.FLAG_UPDATE_CURRENT
        )
        val n = Notification.Builder(this, CHANNEL)
            .setContentTitle("خط التصويب يعمل")
            .setContentText("اضغط إيقاف لإغلاقه")
            .setSmallIcon(android.R.drawable.ic_menu_compass)
            .addAction(Notification.Action.Builder(android.R.drawable.ic_delete, "إيقاف", stop).build())
            .setOngoing(true)
            .build()
        if (Build.VERSION.SDK_INT >= 29)
            startForeground(1, n, ServiceInfo.FOREGROUND_SERVICE_TYPE_MEDIA_PROJECTION)
        else
            startForeground(1, n)
    }

    private fun addOverlay() {
        val v = AimOverlayView(this)
        val lp = WindowManager.LayoutParams(
            WindowManager.LayoutParams.MATCH_PARENT,
            WindowManager.LayoutParams.MATCH_PARENT,
            WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE or
                    WindowManager.LayoutParams.FLAG_NOT_TOUCHABLE or
                    WindowManager.LayoutParams.FLAG_LAYOUT_IN_SCREEN or
                    WindowManager.LayoutParams.FLAG_LAYOUT_NO_LIMITS,
            PixelFormat.TRANSLUCENT
        )
        if (Build.VERSION.SDK_INT >= 28)
            lp.layoutInDisplayCutoutMode =
                WindowManager.LayoutParams.LAYOUT_IN_DISPLAY_CUTOUT_MODE_SHORT_EDGES
        wm.addView(v, lp)
        overlay = v
    }

    /** زر عائم قابل للسحب: ضغطة قصيرة = تشغيل/إيقاف الخط، ضغطة مطوّلة = إغلاق التطبيق. */
    private fun addBubble() {
        val size = (52 * resources.displayMetrics.density).toInt()
        val tv = TextView(this).apply {
            gravity = Gravity.CENTER
            textSize = 12f
            setTextColor(Color.WHITE)
        }
        fun paint() {
            tv.text = if (enabled) "ON" else "OFF"
            tv.background = GradientDrawable().apply {
                shape = GradientDrawable.OVAL
                setColor(if (enabled) Color.argb(230, 20, 140, 60) else Color.argb(230, 170, 30, 30))
                setStroke(3, Color.argb(230, 40, 40, 40))
            }
        }
        paint()
        val lp = WindowManager.LayoutParams(
            size, size,
            WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE or WindowManager.LayoutParams.FLAG_LAYOUT_NO_LIMITS,
            PixelFormat.TRANSLUCENT
        )
        lp.gravity = Gravity.TOP or Gravity.START
        lp.x = 0
        lp.y = (120 * resources.displayMetrics.density).toInt()

        var downX = 0f; var downY = 0f; var startX = 0; var startY = 0
        var moved = false; var downTime = 0L
        tv.setOnTouchListener { _, e ->
            when (e.action) {
                MotionEvent.ACTION_DOWN -> {
                    downX = e.rawX; downY = e.rawY; startX = lp.x; startY = lp.y
                    moved = false; downTime = System.currentTimeMillis()
                }
                MotionEvent.ACTION_MOVE -> {
                    val dx = (e.rawX - downX).toInt(); val dy = (e.rawY - downY).toInt()
                    if (Math.abs(dx) > 12 || Math.abs(dy) > 12) moved = true
                    if (moved) {
                        lp.x = startX + dx; lp.y = startY + dy
                        wm.updateViewLayout(tv, lp)
                    }
                }
                MotionEvent.ACTION_UP -> if (!moved) {
                    if (System.currentTimeMillis() - downTime > 800) {
                        Toast.makeText(this, "تم الإيقاف", Toast.LENGTH_SHORT).show()
                        stopSelf()
                    } else {
                        enabled = !enabled
                        if (!enabled) overlay?.clear()
                        paint()
                    }
                }
            }
            true
        }
        wm.addView(tv, lp)
        bubble = tv
    }

    @Suppress("DEPRECATION")
    private fun realSize(): IntArray {
        val m = DisplayMetrics()
        wm.defaultDisplay.getRealMetrics(m)
        return intArrayOf(m.widthPixels, m.heightPixels, m.densityDpi)
    }

    private fun setupCapture() {
        val s = realSize()
        capW = s[0] / SCALE
        capH = s[1] / SCALE
        px = IntArray(capW * capH)

        reader?.close()
        val r = ImageReader.newInstance(capW, capH, PixelFormat.RGBA_8888, 2)
        reader = r
        r.setOnImageAvailableListener({ ir -> onFrame(ir) }, bg)

        val d = display
        if (d == null) {
            display = projection!!.createVirtualDisplay(
                "aim", capW, capH, s[2],
                DisplayManager.VIRTUAL_DISPLAY_FLAG_AUTO_MIRROR,
                r.surface, null, null
            )
        } else {
            d.resize(capW, capH, s[2])
            d.surface = r.surface
        }
    }

    override fun onConfigurationChanged(newConfig: Configuration) {
        super.onConfigurationChanged(newConfig)
        if (projection != null) main.post { setupCapture() }   // تدوير الشاشة
    }

    private fun onFrame(ir: ImageReader) {
        val img = try { ir.acquireLatestImage() } catch (e: Exception) { null } ?: return
        try {
          try {
            val now = System.currentTimeMillis()
            if (now - lastRun < MIN_INTERVAL_MS) return
            lastRun = now

            val w = img.width
            val h = img.height
            if (w != capW || h != capH) return
            val plane = img.planes[0]
            val ib = plane.buffer.order(java.nio.ByteOrder.LITTLE_ENDIAN).asIntBuffer()
            val rowInts = plane.rowStride / 4
            for (y in 0 until h) {
                ib.position(y * rowInts)
                ib.get(px, y * w, w)
            }
            // RGBA (little-endian int = A B G R) -> 0x00RRGGBB
            for (
