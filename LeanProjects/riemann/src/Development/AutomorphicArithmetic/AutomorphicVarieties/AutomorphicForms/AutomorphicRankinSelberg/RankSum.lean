import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

private lemma UpperTheory.V.Af.Rs.upper_half_plane_point_im (x y : ℝ) (hy : 0 < y) : (UpperTheory.V.Af.Rs.pt x y).im = y := by
  unfold UpperTheory.V.Af.Rs.pt
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  simp

theorem UpperTheory.V.Af.Rs.rankSum :
    UpperTheory.V.Af.Rs.StripFub → UpperTheory.V.Af.Rs.StripInt → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.Pars → UpperTheory.V.Af.Rs.MelSum → UpperTheory.V.Af.Rs.RankSum := by
  intro hFub hInt hNice hPars hMel k L _ f s hs
  have hs1 : 1 < s := hs.1
  have hI := hInt _ (hNice k L f f) s hs
  obtain ⟨hY, -⟩ := hFub _ hI
  have hPa := hPars k L f f
  have hPsum : ∀ y, 0 < y → HasSum (fun n => ‖coef f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n) * y))
      ((∫ x in (0 : ℝ)..1, conj (f (UpperTheory.V.Af.Rs.pt x y)) * f (UpperTheory.V.Af.Rs.pt x y)).re) := by
    intro y hy
    have h := Complex.reCLM.hasSum (hPa y hy)
    have e : (fun n => ‖coef f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n) * y)) =
        fun n => Complex.reCLM (conj (coef f n) * coef f n * (Real.exp (-(4 * Real.pi * n) * y) : ℂ)) := by
      funext n
      rw [Complex.reCLM_apply, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul,
        Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [e]
    simpa only [Complex.reCLM_apply] using h
  have hY2 : IntegrableOn (fun y : ℝ => ((∫ x in (0 : ℝ)..1,
      UpperHalfPlane.petersson (k : ℤ) f f (UpperTheory.V.Af.Rs.pt x y) *
        (((UpperTheory.V.Af.Rs.pt x y).im ^ s : ℝ) : ℂ)) / ((y ^ 2 : ℝ) : ℂ)).re) (Ioi 0) := hY.re
  have hIntP : IntegrableOn (fun y : ℝ =>
      (∫ x in (0 : ℝ)..1, conj (f (UpperTheory.V.Af.Rs.pt x y)) * f (UpperTheory.V.Af.Rs.pt x y)).re *
        y ^ ((k : ℝ) + s - 1 - 1)) (Ioi 0) := by
    refine hY2.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy' : 0 < y := hy
    have him : ∀ x, (UpperTheory.V.Af.Rs.pt x y).im = y := fun x => UpperTheory.V.Af.Rs.upper_half_plane_point_im x y hy'
    have hx : (∫ x in (0 : ℝ)..1, UpperHalfPlane.petersson (k : ℤ) f f (UpperTheory.V.Af.Rs.pt x y) *
        (((UpperTheory.V.Af.Rs.pt x y).im ^ s : ℝ) : ℂ)) =
        (∫ x in (0 : ℝ)..1, conj (f (UpperTheory.V.Af.Rs.pt x y)) * f (UpperTheory.V.Af.Rs.pt x y)) *
          ((y ^ k * y ^ s : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_mul_const]
      congr 1
      funext x
      simp only [UpperHalfPlane.petersson, him x, zpow_natCast]
      push_cast
      ring
    dsimp only
    rw [hx, mul_div_assoc, ← Complex.ofReal_div, Complex.re_mul_ofReal]
    congr 1
    rw [show (k : ℝ) + s - 1 - 1 = ((k : ℝ) + s) - 2 by ring, Real.rpow_sub hy', Real.rpow_add hy',
      Real.rpow_natCast, Real.rpow_two]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact hMel (fun n => ‖coef f n‖ ^ 2) _ ((k : ℝ) + s - 1) (by linarith)
    (fun n => by positivity) hPsum hIntP
