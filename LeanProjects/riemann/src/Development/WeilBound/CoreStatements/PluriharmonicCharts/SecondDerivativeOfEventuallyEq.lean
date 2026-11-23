import Mathlib
open Filter Topology

namespace PositivityTheory.Xgp.fib_hess

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

structure J (f : E → ℝ) (z : E) (v : ℝ) (L : E → ℝ) (B : E → E → ℝ) : Prop where
  cd : ContDiffAt ℝ 2 f z
  val : f z = v
  d1 : ∀ u, fderiv ℝ f z u = L u
  d2 : ∀ u w, fderiv ℝ (fderiv ℝ f) z u w = B u w

theorem hasD {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (w : E) :
    HasFDerivAt (fun y => fderiv ℝ f y w)
      ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ f) z)) z := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) z := hf.fderiv_right (m := 1) (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp z
    (h1.differentiableAt (by norm_num)).hasFDerivAt

theorem evD {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) :
    ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ f y :=
  (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)

theorem hasFDerivAt_of_contDiffAt_two {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) : HasFDerivAt f (fderiv ℝ f z) z :=
  (hf.differentiableAt (by norm_num)).hasFDerivAt

theorem second_derivative_of_eventually_eq {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) {w : E} {k : E → ℝ} {k' : E →L[ℝ] ℝ}
    (he : (fun y => fderiv ℝ f y w) =ᶠ[𝓝 z] k) (hk : HasFDerivAt k k' z) (u : E) :
    fderiv ℝ (fderiv ℝ f) z u w = k' u := by
  have := (hasD hf w).unique (hk.congr_of_eventuallyEq he)
  rw [← this]; rfl

theorem J.congr {f : E → ℝ} {z : E} {v v' : ℝ} {L L' : E → ℝ} {B B' : E → E → ℝ}
    (h : J f z v L B) (hv : v = v') (hL : ∀ u, L u = L' u) (hB : ∀ u w, B u w = B' u w) :
    J f z v' L' B' :=
  ⟨h.cd, h.val.trans hv, fun u => (h.d1 u).trans (hL u), fun u w => (h.d2 u w).trans (hB u w)⟩

theorem J.add {f g : E → ℝ} {z : E} {v v' : ℝ} {L L' : E → ℝ} {B B' : E → E → ℝ}
    (hf : J f z v L B) (hg : J g z v' L' B') :
    J (fun y => f y + g y) z (v + v') (fun u => L u + L' u) (fun u w => B u w + B' u w) := by
  have hc : ContDiffAt ℝ 2 (fun y => f y + g y) z := hf.cd.add hg.cd
  refine ⟨hc, by rw [hf.val, hg.val], fun u => ?_, fun u w => ?_⟩
  · have := ((hasFDerivAt_of_contDiffAt_two hf.cd).fun_add (hasFDerivAt_of_contDiffAt_two hg.cd)).fderiv
    rw [this]; simp [hf.d1, hg.d1]
  · have he : (fun y => fderiv ℝ (fun y => f y + g y) y w) =ᶠ[𝓝 z]
        fun y => fderiv ℝ f y w + fderiv ℝ g y w := by
      filter_upwards [evD hf.cd, evD hg.cd] with y h1 h2
      rw [(h1.hasFDerivAt.fun_add h2.hasFDerivAt).fderiv]; simp
    rw [second_derivative_of_eventually_eq hc he ((hasD hf.cd w).fun_add (hasD hg.cd w))]
    simp [hf.d2, hg.d2]

theorem J.mul {f g : E → ℝ} {z : E} {v v' : ℝ} {L L' : E → ℝ} {B B' : E → E → ℝ}
    (hf : J f z v L B) (hg : J g z v' L' B') :
    J (fun y => f y * g y) z (v * v') (fun u => v * L' u + v' * L u)
      (fun u w => v * B' u w + v' * B u w + L u * L' w + L w * L' u) := by
  have hc : ContDiffAt ℝ 2 (fun y => f y * g y) z := hf.cd.mul hg.cd
  refine ⟨hc, by rw [hf.val, hg.val], fun u => ?_, fun u w => ?_⟩
  · have := ((hasFDerivAt_of_contDiffAt_two hf.cd).fun_mul (hasFDerivAt_of_contDiffAt_two hg.cd)).fderiv
    rw [this]; simp [hf.d1, hg.d1, hf.val, hg.val]
  · have he : (fun y => fderiv ℝ (fun y => f y * g y) y w) =ᶠ[𝓝 z]
        fun y => f y * fderiv ℝ g y w + g y * fderiv ℝ f y w := by
      filter_upwards [evD hf.cd, evD hg.cd] with y h1 h2
      rw [(h1.hasFDerivAt.fun_mul h2.hasFDerivAt).fderiv]; simp
    rw [second_derivative_of_eventually_eq hc he (((hasFDerivAt_of_contDiffAt_two hf.cd).fun_mul (hasD hg.cd w)).fun_add
      ((hasFDerivAt_of_contDiffAt_two hg.cd).fun_mul (hasD hf.cd w)))]
    simp [hf.d1, hg.d1, hf.d2, hg.d2, hf.val, hg.val]
    ring

theorem J.const (c : ℝ) (z : E) : J (fun _ : E => c) z c (fun _ => 0) (fun _ _ => 0) := by
  refine ⟨contDiffAt_const, rfl, fun u => by simp, fun u w => by simp⟩

theorem J.clm (T : E →L[ℝ] ℝ) (z : E) : J (fun y => T y) z (T z) (fun u => T u) (fun _ _ => 0) := by
  have h : fderiv ℝ (fun y => T y) = fun _ => T := funext fun y => T.fderiv
  refine ⟨T.contDiff.contDiffAt, rfl, fun u => by rw [h], fun u w => by rw [h]; simp⟩

theorem J.log {f : E → ℝ} {z : E} {v : ℝ} {L : E → ℝ} {B : E → E → ℝ}
    (hf : J f z v L B) (hv : v ≠ 0) :
    J (fun y => Real.log (f y)) z (Real.log v) (fun u => v⁻¹ * L u)
      (fun u w => v⁻¹ * B u w - L u * L w / v ^ 2) := by
  have hz : f z ≠ 0 := by rw [hf.val]; exact hv
  have hc : ContDiffAt ℝ 2 (fun y => Real.log (f y)) z := hf.cd.log hz
  refine ⟨hc, by rw [hf.val], fun u => ?_, fun u w => ?_⟩
  · have := ((hasFDerivAt_of_contDiffAt_two hf.cd).log hz).fderiv
    rw [this]; simp [hf.d1, hf.val]
  · have he : (fun y => fderiv ℝ (fun y => Real.log (f y)) y w) =ᶠ[𝓝 z]
        fun y => (f y)⁻¹ * fderiv ℝ f y w := by
      filter_upwards [evD hf.cd, hf.cd.continuousAt.eventually_ne hz] with y h1 h2
      rw [(h1.hasFDerivAt.log h2).fderiv]; simp
    have hi : HasFDerivAt (fun y => (f y)⁻¹) ((-((f z) ^ 2)⁻¹) • fderiv ℝ f z) z :=
      (hasDerivAt_inv hz).comp_hasFDerivAt z (hasFDerivAt_of_contDiffAt_two hf.cd)
    rw [second_derivative_of_eventually_eq hc he (hi.fun_mul (hasD hf.cd w))]
    simp [hf.d1, hf.d2, hf.val]
    ring

theorem J.comp {f : F → ℝ} (T : E →L[ℝ] F) {z : E} {v : ℝ} {L : F → ℝ} {B : F → F → ℝ}
    (hf : J f (T z) v L B) :
    J (fun y => f (T y)) z v (fun u => L (T u)) (fun u w => B (T u) (T w)) := by
  have hc : ContDiffAt ℝ 2 (fun y => f (T y)) z := hf.cd.comp z T.contDiff.contDiffAt
  refine ⟨hc, hf.val, fun u => ?_, fun u w => ?_⟩
  · have : HasFDerivAt (fun y => f (T y)) _ z := (hasFDerivAt_of_contDiffAt_two hf.cd).comp z T.hasFDerivAt
    rw [this.fderiv]; simp [hf.d1]
  · have he : (fun y => fderiv ℝ (fun y => f (T y)) y w) =ᶠ[𝓝 z]
        fun y => fderiv ℝ f (T y) (T w) := by
      filter_upwards [T.continuous.continuousAt.eventually (evD hf.cd)] with y h1
      have : HasFDerivAt (fun y => f (T y)) _ y := h1.hasFDerivAt.comp y T.hasFDerivAt
      rw [this.fderiv]; simp
    have hk : HasFDerivAt (fun y => fderiv ℝ f (T y) (T w)) _ z :=
      (hasD hf.cd (T w)).comp z T.hasFDerivAt
    rw [second_derivative_of_eventually_eq hc he hk]
    simp [hf.d2]

theorem J.atom {g : E → ℂ} {z : E} (hg : ContDiffAt ℝ 2 g z) (h0 : fderiv ℝ g z = 0)
    (l : ℂ →L[ℝ] ℝ) :
    J (fun y => l (g y)) z (l (g z)) (fun _ => 0)
      (fun u w => fderiv ℝ (fderiv ℝ (fun y => l (g y))) z u w) := by
  refine ⟨l.contDiff.contDiffAt.comp z hg, rfl, fun u => ?_, fun u w => rfl⟩
  have : HasFDerivAt (fun y => l (g y)) _ z :=
    l.hasFDerivAt.comp z (hg.differentiableAt (by norm_num)).hasFDerivAt
  rw [this.fderiv, h0]; simp

theorem J.neg {f : E → ℝ} {z : E} {v : ℝ} {L : E → ℝ} {B : E → E → ℝ}
    (hf : J f z v L B) : J (fun y => -f y) z (-v) (fun u => -L u) (fun u w => -B u w) := by
  have := (J.const (-1 : ℝ) z).mul hf
  simp only [neg_mul, one_mul] at this
  exact this.congr rfl (fun u => by ring) (fun u w => by ring)

theorem main_jet {z : E} {x w A00 A01 A10 A11 B00 upperOffDiagonalCoeff lowerOffDiagonalCoeff ToralGalois : E → ℝ} {x0 w0 : ℝ}
    {Lx Lw : E → ℝ} {a00 a01 a10 a11 b00 b01 b10 b11 : E → E → ℝ}
    (hx : J x z x0 Lx (fun _ _ => 0)) (hw : J w z w0 Lw (fun _ _ => 0))
    (h00 : J A00 z 1 (fun _ => 0) a00) (h01 : J A01 z 0 (fun _ => 0) a01)
    (h10 : J A10 z 0 (fun _ => 0) a10) (h11 : J A11 z 1 (fun _ => 0) a11)
    (k00 : J B00 z 0 (fun _ => 0) b00) (k01 : J upperOffDiagonalCoeff z 0 (fun _ => 0) b01)
    (k10 : J lowerOffDiagonalCoeff z 0 (fun _ => 0) b10) (k11 : J ToralGalois z 0 (fun _ => 0) b11)
    {φ : E → ℝ}
    (hφ : ∀ y, φ y = -Real.log (A00 y + x y * (A01 y + A10 y) + w y * (lowerOffDiagonalCoeff y + -upperOffDiagonalCoeff y)
        + (x y * x y + w y * w y) * A11 y)
      + (1 / 2) * Real.log (A00 y * A11 y + -(B00 y * ToralGalois y) + -(A01 y * A10 y) + upperOffDiagonalCoeff y * lowerOffDiagonalCoeff y)) :
    ContDiffAt ℝ 2 φ z ∧ ∀ u v, fderiv ℝ (fderiv ℝ φ) z u v =
      -((1 + (x0 ^ 2 + w0 ^ 2))⁻¹ * (a00 u v + x0 * (a01 u v + a10 u v) + w0 * (b10 u v - b01 u v)
          + (x0 ^ 2 + w0 ^ 2) * a11 u v + 2 * (Lx u * Lx v + Lw u * Lw v))
        - (2 * x0 * Lx u + 2 * w0 * Lw u) * (2 * x0 * Lx v + 2 * w0 * Lw v)
          / (1 + (x0 ^ 2 + w0 ^ 2)) ^ 2) + (1 / 2) * (a00 u v + a11 u v) := by
  have hh : J (fun y => A00 y + x y * (A01 y + A10 y) + w y * (lowerOffDiagonalCoeff y + -upperOffDiagonalCoeff y)
        + (x y * x y + w y * w y) * A11 y) z (1 + (x0 ^ 2 + w0 ^ 2))
        (fun u => 2 * x0 * Lx u + 2 * w0 * Lw u)
        (fun u v => a00 u v + x0 * (a01 u v + a10 u v) + w0 * (b10 u v - b01 u v)
          + (x0 ^ 2 + w0 ^ 2) * a11 u v + 2 * (Lx u * Lx v + Lw u * Lw v)) :=
    (((h00.add (hx.mul (h01.add h10))).add (hw.mul (k10.add k01.neg))).add
      (((hx.mul hx).add (hw.mul hw)).mul h11)).congr (by ring) (fun u => by ring)
      (fun u v => by ring)
  have hD : J (fun y => A00 y * A11 y + -(B00 y * ToralGalois y) + -(A01 y * A10 y) + upperOffDiagonalCoeff y * lowerOffDiagonalCoeff y) z 1
      (fun _ => 0) (fun u v => a00 u v + a11 u v) :=
    ((((h00.mul h11).add (k00.mul k11).neg).add (h01.mul h10).neg).add (k01.mul k10)).congr
      (by ring) (fun u => by ring) (fun u v => by ring)
  have hpos : (1 + (x0 ^ 2 + w0 ^ 2)) ≠ 0 := by positivity
  have hJ := (hh.log hpos).neg.add ((J.const (1 / 2 : ℝ) z).mul (hD.log one_ne_zero))
  obtain rfl : φ = _ := funext hφ
  refine ⟨hJ.cd, fun u v => (hJ.d2 u v).trans ?_⟩
  ring

end PositivityTheory.Xgp.fib_hess
