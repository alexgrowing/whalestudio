import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RamifiedPrimePowersSizeBounds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBoundsStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn.ScalSize

variable {D : D7} {j : ℕ}

theorem one_le_f (D : D7) : (1 : ℝ) ≤ D.R.f := by
  have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  exact_mod_cast this

theorem one_le_r (D : D7) : (1 : ℝ) ≤ D.R.r := by
  have : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact_mod_cast this

theorem size_eq (w : WeightFamilies.Wt D j) :
    w.size = (WeightAlgebra.DF w : ℝ) + (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1 := by
  unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
  push_cast
  ring

theorem size_ge (w : WeightFamilies.Wt D j) : (WeightAlgebra.DF w : ℝ) + (D.R.f : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1 ≤ w.size := by
  rw [size_eq]
  have h1 : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  have h2 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]

theorem n_le_size (w : WeightFamilies.Wt D j) : (w.n : ℝ) ≤ w.size := by
  have h := size_ge w
  have h1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le (one_le_f D) (one_le_r D)
  have h2 : (0 : ℝ) ≤ w.n := by positivity
  have h3 : (0 : ℝ) ≤ WeightAlgebra.DF w := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

theorem size_comb (T : ℕ) (wL wF : WeightFamilies.Wt D j) :
    (wadd wF (wsmul T wL)).size + T = T * wL.size + wF.size := by
  unfold WeightFamilies.Wt.size
  simp only [wadd, wsmul]
  push_cast
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  ring

theorem log_zOwn_le (p : ℕ) (hp : 0 < p) (w : WeightFamilies.Wt D j) :
    Real.log (zOwnP D p w : ℝ) ≤ 2 * Real.log p * w.size := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h := size_ge w
  have h3 : (0 : ℝ) ≤ WeightAlgebra.DF w := by positivity
  unfold zOwnP
  push_cast
  rw [Real.log_pow]
  push_cast
  have : (WeightAlgebra.DF w : ℝ) + 2 * D.R.f * D.R.r * w.n ≤ 2 * w.size := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hl]

theorem lamStar_nonneg (w : WeightFamilies.Wt D j) : 0 ≤ lamStar D := by
  obtain ⟨-, -, h1, h2, -⟩ := GlobalTheory.RunIn.pPow_size D j w
  unfold lamStar
  linarith

noncomputable def comb (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) : 𝓞 B.KO :=
  (zOwnP D p G : 𝓞 B.KO) * sOf B hinj EX wL ^ T * sOf B hinj EX wF

theorem comb_eq (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) :
    (zOwnP D p G : 𝓞 B.KO) * nnW B hinj EX wL ^ T * nnW B hinj EX wF *
      (pPow D (T * c2 D wL + c2 D wF) (T * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF)
        (T * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF) : 𝓞 B.KO) = comb B hinj EX p G wL wF T := by
  unfold comb sOf pPow
  push_cast
  ring

theorem comb_ne_zero (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (hp : 0 < p)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) : comb B hinj EX p G wL wF T ≠ 0 := by
  unfold comb
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wL).1)) (GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wF).1
  exact Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')

theorem log_comb_le (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (hp : 0 < p)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) (σ : B.KO →+* ℂ) :
    Real.log ‖σ (comb B hinj EX p G wL wF T : B.KO)‖ ≤
      2 * Real.log p * G.size + lamStar D * (T * wL.size + wF.size) := by
  obtain ⟨hL0, hL⟩ := GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wL
  obtain ⟨hF0, hF⟩ := GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wF
  have hL1 := (hL σ).2.2.2
  have hF1 := (hF σ).2.2.2
  have nz : ∀ x : 𝓞 B.KO, x ≠ 0 → ‖σ (x : B.KO)‖ ≠ 0 := fun x hx => by
    rw [norm_ne_zero_iff, map_ne_zero]
    exact_mod_cast hx
  have hz : (zOwnP D p G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')
  have e : ‖σ (comb B hinj EX p G wL wF T : B.KO)‖ =
      (zOwnP D p G : ℝ) * ‖σ (sOf B hinj EX wL : B.KO)‖ ^ T * ‖σ (sOf B hinj EX wF : B.KO)‖ := by
    unfold comb
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, norm_mul, norm_pow,
      Complex.norm_natCast]
  rw [e, Real.log_mul (mul_ne_zero hz (pow_ne_zero _ (nz _ hL0))) (nz _ hF0),
    Real.log_mul hz (pow_ne_zero _ (nz _ hL0)), Real.log_pow]
  have h1 := log_zOwn_le p hp G
  have hT : (0 : ℝ) ≤ T := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hL1 hT]

theorem log_comb_le' (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (hp : 0 < p)
    (wL wF : WeightFamilies.Wt D j) (hn : 1 ≤ wL.n) (T : ℕ) (σ : B.KO →+* ℂ) :
    Real.log ‖σ (comb B hinj EX p (wadd wF (wsmul T wL)) wL wF T : B.KO)‖ ≤
      2 * (lamStar D + 2 * Real.log p) * (wadd wF (wsmul T wL)).size := by
  have h := log_comb_le B hinj EX p hp (wadd wF (wsmul T wL)) wL wF T σ
  rw [← size_comb] at h
  have h1 := n_le_size (wadd wF (wsmul T wL))
  have h2 : T ≤ (wadd wF (wsmul T wL)).n := by
    simp only [wadd, wsmul]
    nlinarith
  have h3 : (T : ℝ) ≤ (wadd wF (wsmul T wL)).size := le_trans (by exact_mod_cast h2) h1
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hΛ := lamStar_nonneg wL
  have hs := (wadd wF (wsmul T wL)).one_le_size
  nlinarith [mul_le_mul_of_nonneg_left h3 hΛ, mul_nonneg hl (le_trans zero_le_one hs)]

theorem wt_eq {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} (hF : IsF' ka wL wF T nP) (hL : wL.n = nW)
    (hn : ka.n = nP + T * nW) : ka = wadd wF (wsmul T wL) := by
  obtain ⟨h1, h2, h3⟩ := hF
  obtain ⟨a, b, _, _, n, _⟩ := ka
  have e1 : a = (wadd wF (wsmul T wL)).aP := funext fun τ => funext fun i => by
    have := h2 τ i
    simp only [wadd, wsmul] at this ⊢
    zify
    linarith
  have e2 : b = (wadd wF (wsmul T wL)).aM := funext fun τ => funext fun i => by
    have := h3 τ i
    simp only [wadd, wsmul] at this ⊢
    zify
    linarith
  have e3 : n = (wadd wF (wsmul T wL)).n := by
    simp only [wadd, wsmul] at hn ⊢
    rw [h1, hL, hn]
  subst e1 e2 e3
  rfl

end GlobalTheory.RunIn.ScalSize

open GlobalTheory.RunIn.ScalSize in

theorem GlobalTheory.RunIn.scalOfP_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ), 0 < p → 1 ≤ nW → wL.n = nW → IsF' ka wL wF Tn nP → ka.n = nP + Tn * nW → (scalOfP B hinj EX p ka wL wF Tn).sF ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).s0 ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).sK ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, (Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sW : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wL.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sF : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).s0 : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * (wadd wF (wsmul (WeightFamilies.dimY D j) wL)).size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sK : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * ka.size) := by
  intro D B hinj EX j p ka wL wF Tn nP nW hp hW hL hF hn
  have eF : (scalOfP B hinj EX p ka wL wF Tn).sF = comb B hinj EX p wF wL wF 0 := by
    unfold comb sOf
    simp only [scalOfP, pow_zero, mul_one, mul_assoc]
  have e0 : (scalOfP B hinj EX p ka wL wF Tn).s0 =
      comb B hinj EX p (wadd wF (wsmul (WeightFamilies.dimY D j) wL)) wL wF (WeightFamilies.dimY D j) := comb_eq ..
  have eK : (scalOfP B hinj EX p ka wL wF Tn).sK = comb B hinj EX p ka wL wF Tn := comb_eq ..
  have hn1 : 1 ≤ wL.n := hL ▸ hW
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rw [eF, e0, eK, sW_eq_sOf]
  refine ⟨comb_ne_zero B hinj EX p hp _ _ _ _, comb_ne_zero B hinj EX p hp _ _ _ _,
    comb_ne_zero B hinj EX p hp _ _ _ _, fun σ => ⟨?_, ?_, log_comb_le' B hinj EX p hp wL wF hn1 _ σ, ?_⟩⟩
  · have h := ((GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wL).2 σ).2.2.2
    nlinarith [mul_nonneg hl (le_trans zero_le_one wL.one_le_size)]
  · have h := log_comb_le B hinj EX p hp wF wL wF 0 σ
    push_cast at h
    linarith
  · rw [wt_eq hF hL hn]
    exact log_comb_le' B hinj EX p hp wL wF hn1 _ σ
