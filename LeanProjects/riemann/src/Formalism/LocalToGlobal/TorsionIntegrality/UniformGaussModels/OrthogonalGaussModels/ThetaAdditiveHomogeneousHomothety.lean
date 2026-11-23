import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementM
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormTwelveCubedEqOneOfFiveLePrime
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy jInv)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.InvariantFactorPaths.G7 (at1)

theorem good_model_uniform_homothety : GoodModelUniform := by
  intro dK L hsq hd4 hcm
  have hD0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := Formalism.L2.Th1.F.discNeZero L
  obtain ⟨c, hc12⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (show 0 < 12 by norm_num)
  have hc : c ≠ 0 := by
    intro h
    rw [h] at hc12
    exact hD0 (by rw [← hc12]; simp)
  refine ⟨c, hc, ?_⟩
  intro p _ h5 ι
  have hH := Formalism.L2.Th1.F.homogeneity L c hc
  have e2 : (Formalism.L2.Th1.F.scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := hH.2.2.2.2.2.2.2.2.2.1
  have e3 : (Formalism.L2.Th1.F.scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := hH.2.2.2.2.2.2.2.2.2.2
  set a : ℂ := (Formalism.L2.Th1.F.scalePair L c hc).g₂ with ha
  set b : ℂ := (Formalism.L2.Th1.F.scalePair L c hc).g₃ with hb

  have hΔ : a ^ 3 - 27 * b ^ 2 = 1 := by
    rw [e2, e3]
    have : ((c ^ 4)⁻¹ * L.g₂) ^ 3 - 27 * ((c ^ 6)⁻¹ * L.g₃) ^ 2 =
        (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
      field_simp
    rw [this, hc12, inv_mul_cancel₀ hD0]
  have hj : 1728 * a ^ 3 = jInv L := by
    unfold jInv
    rw [e2, ← hc12]
    field_simp
  have hJ : ‖ι (jInv L)‖ ≤ 1 :=
    ReciprocityTheory.ChartRestriction.L1.jInt dK L hsq hd4 hcm p ι
  have ha3 : ‖ι a‖ ^ 3 ≤ 1 := by
    have h := congrArg ι hj
    rw [map_mul, map_pow, map_ofNat] at h
    rw [← h, norm_mul, GM.norm_twelve_cubed_eq_one_of_five_le_prime p h5, one_mul, norm_pow] at hJ
    exact hJ
  have ha1 : ‖ι a‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 ha3
  have hb2 : ‖ι b‖ ^ 2 ≤ 1 := by
    have h : 27 * ι b ^ 2 = ι a ^ 3 - 1 := by
      have h := congrArg ι hΔ
      rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
      linear_combination -h
    have h' := congrArg norm h
    rw [norm_mul, GM.norm_27 p h5, one_mul, norm_pow] at h'
    rw [h', sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by simp))
    rw [norm_pow]; exact ha3
  have hb1 : ‖ι b‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hb2
  unfold curveL
  refine Formalism.L2.Th1.E.ScaledModelNorms.intCurve_short p h5 _ _ ha1 hb1 ?_
  have h := congrArg ι hΔ
  rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
  rw [h, norm_one]

namespace ThetaHomothety

open Formalism.L2.Th1.F (scalePair opU herm th0 area taylor0 sgStar)

open Classical in

theorem coeff_single_variable_series {K n : Type} [Field K] (i : n) (f : PowerSeries K) (e : n →₀ ℕ) :
    MvPowerSeries.coeff e (at1 i f) =
      if e = Finsupp.single i (e i) then PowerSeries.coeff (e i) f else 0 := by
  rw [Formalism.InvariantFactorPaths.G7.at1, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [finsum_eq_single _ (e i) (fun d hd => by
    beta_reduce
    exact if_neg (fun h => hd (by rw [h, Finsupp.single_eq_same])))]

theorem rescale_single_variable_series {K n : Type} [Field K] (a : n → K) (i : n) (f : PowerSeries K) :
    MvPowerSeries.rescale a (at1 i f) = at1 i (PowerSeries.rescale (a i) f) := by
  classical
  ext e
  rw [MvPowerSeries.coeff_rescale, coeff_single_variable_series, coeff_single_variable_series, PowerSeries.coeff_rescale]
  split_ifs with h
  · conv_lhs => rw [h]
    simp [Finsupp.prod_single_index]
  · simp

theorem rescale_thetaProd {K κ n : Type} [Field K] [Fintype κ] [Fintype n] (a : n → K) (r : κ → K)
    (H : κ → n → PowerSeries K) :
    MvPowerSeries.rescale a (Formalism.L2.Th1.E.thetaProd r H) =
      Formalism.L2.Th1.E.thetaProd r (fun k i => PowerSeries.rescale (a i) (H k i)) := by
  have hC : ∀ x : K, MvPowerSeries.rescale a (MvPowerSeries.C x) = MvPowerSeries.C x := by
    classical
    intro x
    ext e
    rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]
    split_ifs with h
    · subst h
      simp
    · simp
  simp only [Formalism.L2.Th1.E.thetaProd, map_sum, map_mul, map_prod, hC, rescale_single_variable_series]

theorem herm_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z x : ℂ) :
    herm (scalePair L c hc) (c * z) (c * x) = herm L z x := by
  exact Formalism.L2.Th1.F.Homog.herm_scale (L := L) (c := c) (hc := hc) z x

theorem opU_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ s z : ℂ) :
    opU (scalePair L c hc) (c * s) (th0 (scalePair L c hc) (c * ω₀ / 2)) (c * z) =
      opU L s (th0 L (ω₀ / 2)) z := by
  unfold opU
  rw [herm_scale L c hc z s, herm_scale L c hc s s]
  have h1 : c * ω₀ / 2 = c * (ω₀ / 2) := by ring
  have h2 : c * z + c * s = c * (z + s) := by ring
  rw [h1, h2, Formalism.L2.Th1.F.Homog.normalizedTheta_scale (L := L) (c := c) (hc := hc)]

theorem differentiable_opU (L : PeriodPair) (s : ℂ) {θ : ℂ → ℂ} (h : Differentiable ℂ θ) :
    Differentiable ℂ (opU L s θ) := by
  show Differentiable ℂ fun z =>
    θ (z + s) * Complex.exp (-(Real.pi : ℂ) * herm L z s - (Real.pi : ℂ) * herm L s s / 2)
  simp only [herm]
  fun_prop

theorem differentiable_evenTheta (L : PeriodPair) (t : ℂ) : Differentiable ℂ (th0 L t) := by
  have hs : Differentiable ℂ (sgStar L) := (Formalism.L2.Th1.F.sgStarBasic L).1
  show Differentiable ℂ fun z => opU L t (sgStar L) z / opU L t (sgStar L) 0
  exact (differentiable_opU L t hs).div_const _

theorem taylor0_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ s : ℂ) :
    PowerSeries.rescale c
        (taylor0 (opU (scalePair L c hc) (c * s) (th0 (scalePair L c hc) (c * ω₀ / 2)))) =
      taylor0 (opU L s (th0 L (ω₀ / 2))) := by
  have hd : Differentiable ℂ
      (opU (scalePair L c hc) (c * s) (th0 (scalePair L c hc) (c * ω₀ / 2))) :=
    differentiable_opU _ _ (differentiable_evenTheta _ _)
  have hF : (fun z => opU (scalePair L c hc) (c * s) (th0 (scalePair L c hc) (c * ω₀ / 2)) (c * z)) =
      opU L s (th0 L (ω₀ / 2)) := funext (opU_scale L c hc ω₀ s)
  ext n
  simp only [taylor0, PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
  rw [← hF, iteratedDeriv_comp_const_mul hd.contDiff c]
  simp only [mul_zero]
  ring

end ThetaHomothety

theorem theta_additive_homogeneous_homothety : ThetaZScale := by
  unfold ThetaZScale
  intro p _ L ι c hc ω₀ _ κ n _ _ r s
  unfold thetaZ
  rw [ThetaHomothety.rescale_thetaProd]
  congr 1
  funext k i
  ext m
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_map,
    ← ThetaHomothety.taylor0_scale L c hc ω₀ (s k i), PowerSeries.coeff_rescale, map_mul, map_pow]
  rfl

end Formalism.L2.Th1.Top
