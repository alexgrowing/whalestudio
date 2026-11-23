import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.AnalyticIdentityTheoremsZetaFacts
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaConv
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaBasic
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaLog
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc

noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F

namespace TaylorSigmaUniqueness

open PowerSeries in

lemma formal_unique (P U V : PowerSeries ℂ) (hV : X * derivative ℂ V = -(X * P))
    (hV0 : constantCoeff V = 0) (hU : X * derivative ℂ U = X * (V * U))
    (hU0 : constantCoeff U = 1) : U = B.fExp (B.sigS P) := by
  have hV' : derivative ℂ V = -P := by
    apply mul_left_cancel₀ (X_ne_zero (R := ℂ))
    rw [hV, mul_neg]
  have hU' : derivative ℂ U = V * U := mul_left_cancel₀ (X_ne_zero (R := ℂ)) hU
  have hVp : V = -B.prim P := by
    refine derivative.ext ?_ ?_
    · rw [hV', map_neg]
      exact congrArg Neg.neg (B.dz_prim P).symm
    · rw [hV0, map_neg, B.constantCoeff_prim, neg_zero]
  have hS0 : constantCoeff (B.sigS P) = 0 := by
    rw [B.sigS, map_neg, B.constantCoeff_prim, neg_zero]
  have hS0' : constantCoeff (-B.sigS P) = 0 := by rw [map_neg, hS0, neg_zero]
  have hSd : derivative ℂ (B.sigS P) = V := by
    rw [B.sigS, map_neg, hVp]
    exact congrArg Neg.neg (B.dz_prim _)
  have key : U * (C.mvExp (-B.sigS P) : PowerSeries ℂ) = 1 := by
    refine derivative.ext ?_ ?_
    · rw [Derivation.leibniz, C.derivative_mvExp hS0', map_neg, hSd, hU', Derivation.map_one_eq_zero]
      simp only [smul_eq_mul]
      ring
    · rw [map_mul, hU0, map_one, one_mul]
      exact C.constantCoeff_mvExp hS0'
  have h2 : (C.mvExp (-B.sigS P) : PowerSeries ℂ) * C.mvExp (B.sigS P) = 1 := C.mvExp_neg hS0
  calc U = U * ((C.mvExp (-B.sigS P) : PowerSeries ℂ) * C.mvExp (B.sigS P)) := by rw [h2, mul_one]
    _ = C.mvExp (B.sigS P) := by rw [← mul_assoc, key, one_mul]
    _ = B.fExp (B.sigS P) := rfl

lemma constantCoeff_taylor0 (f : ℂ → ℂ) : PowerSeries.constantCoeff (taylor0 f) = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, taylor0, PowerSeries.coeff_mk]
  simp

def u (L : PeriodPair) (z : ℂ) : ℂ := ∏' l : L.lattice, wFactor (l : ℂ) z

lemma differentiable_u (L : PeriodPair) : Differentiable ℂ (u L) :=
  SigmaBasic.differentiable_tprod sigma_product_locally_uniform L

lemma u_zero (L : PeriodPair) : u L 0 = 1 := by
  simp [u, SigmaBasic.wFactor_zero_right]

lemma analyticAt_v (L : PeriodPair) : AnalyticAt ℂ (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) 0 :=
  (AnalyticIdentityTheoremsZetaFacts.differentiableOn_zetaExcept L 0).analyticAt (L.compl_lattice_sdiff_singleton_mem_nhds 0)

lemma analyticAt_pExcept (L : PeriodPair) : AnalyticAt ℂ (L.weierstrassPExcept 0) 0 :=
  (L.differentiableOn_weierstrassPExcept 0).analyticAt (L.compl_lattice_sdiff_singleton_mem_nhds 0)

lemma ode_u (L : PeriodPair) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv (u L) z = z * (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 z * u L z) := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases h0 : z = 0
  · simp [h0]
  have hzl : z ∉ L.lattice := fun h => hz ⟨h, h0⟩
  have h1 : HasDerivAt (wSigma L) (wZeta L z * wSigma L z) z :=
    sigmaLogDeriv_of sigma_product_locally_uniform sigma_summable zeta_summable L z hzl
  have h2 : HasDerivAt (wSigma L) (1 * u L z + z * deriv (u L) z) z :=
    (hasDerivAt_id z).mul (differentiable_u L z).hasDerivAt
  have h3 := h1.unique h2
  rw [← AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_add L z] at h3
  have h4 : wSigma L z = z * u L z := rfl
  rw [h4] at h3
  have h5 : (1 / z) * z = 1 := by field_simp
  linear_combination -h3 + u L z * h5

lemma ode_v (L : PeriodPair) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) z = -(z * L.weierstrassPExcept 0 z) := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases h0 : z = 0
  · simp [h0]
  have hzl : z ∉ L.lattice := fun h => hz ⟨h, h0⟩
  have h1 : HasDerivAt (wZeta L) (-(L.weierstrassP z)) z := zeta_has_deriv L z hzl
  have h2 : HasDerivAt (fun w : ℂ => 1 / w) (-(1 / z ^ 2)) z := by
    simpa only [one_div] using hasDerivAt_inv h0
  have h3 : AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 = fun w => wZeta L w - 1 / w := by
    funext w
    rw [← AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_add L w]
    ring
  have h4 : deriv (fun w => wZeta L w - 1 / w) z = -(L.weierstrassP z) - -(1 / z ^ 2) :=
    (h1.sub h2).deriv
  rw [h3, h4]
  have h5 := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h5
  rw [← h5]
  ring

end TaylorSigmaUniqueness

open TaylorSigmaUniqueness in

theorem taylorSigma_of (hr : TaylorRing) (hd : TaylorDeriv) : TaylorSigma := by
  intro L
  obtain ⟨hadd, hC, hX, hgerm⟩ := hr
  have hid : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hu : AnalyticAt ℂ (u L) 0 := (differentiable_u L).analyticAt 0
  have hv := analyticAt_v L
  have hp := analyticAt_pExcept L
  have e1 : taylor0 (wSigma L) = PowerSeries.X * taylor0 (u L) := by
    have := (hadd (fun z => z) (u L) hid hu).2
    rw [hX] at this
    exact this
  have eU : PowerSeries.X * PowerSeries.derivative ℂ (taylor0 (u L))
      = PowerSeries.X * (taylor0 (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) * taylor0 (u L)) := by
    have hvu : AnalyticAt ℂ (fun z => AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 z * u L z) 0 := hv.mul hu
    rw [← hd.1 _ hu, ← hX, ← (hadd _ _ hid hu.deriv).2, ← (hadd _ _ hv hu).2,
      ← (hadd _ _ hid hvu).2]
    exact hgerm _ _ (ode_u L)
  have eV : PowerSeries.X * PowerSeries.derivative ℂ (taylor0 (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0))
      = -(PowerSeries.X * pSeries L) := by
    have hneg : taylor0 (fun z => (-1 : ℂ) * (z * L.weierstrassPExcept 0 z))
        = -(PowerSeries.X * pSeries L) := by
      have hzp : AnalyticAt ℂ (fun z => z * L.weierstrassPExcept 0 z) 0 := hid.mul hp
      rw [(hadd (fun _ => (-1 : ℂ)) _ analyticAt_const hzp).2, hC,
        (hadd _ _ hid hp).2, hX, pSeries]
      simp
    rw [← hd.1 _ hv, ← hneg, ← hX, ← (hadd _ _ hid hv.deriv).2]
    refine hgerm _ _ ((ode_v L).mono fun z hz => ?_)
    show z * deriv (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) z = -1 * (z * L.weierstrassPExcept 0 z)
    rw [hz]; ring
  rw [e1, B.sigma]
  congr 1
  refine formal_unique (pSeries L) _ _ eV ?_ eU ?_
  · rw [constantCoeff_taylor0, AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_zero]
  · rw [constantCoeff_taylor0, u_zero]

theorem taylorSgStar_of (h : TaylorSigma) (hr : TaylorRing) (he : TaylorExp) (hent : SigmaEntire) :
    TaylorSgStar := by
  intro L
  obtain ⟨hadd, hC, hX, -⟩ := hr
  have hid : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hzz : AnalyticAt ℂ (fun z : ℂ => z * z) 0 := hid.mul hid
  have hf : AnalyticAt ℂ (fun z : ℂ => -(s2 L / 2) * (z * z)) 0 := analyticAt_const.mul hzz
  have hef : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-(s2 L / 2) * (z * z))) 0 := hf.cexp
  have hTf : taylor0 (fun z : ℂ => -(s2 L / 2) * (z * z))
      = -(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) := by
    rw [(hadd (fun _ => -(s2 L / 2)) _ analyticAt_const hzz).2, hC,
      (hadd _ _ hid hid).2, hX, map_neg]
    ring
  have hfun : sgStar L = fun z => wSigma L z * Complex.exp (-(s2 L / 2) * (z * z)) := by
    funext z
    rw [sgStar]
    congr 2
    ring
  rw [hfun, (hadd _ _ ((hent L).analyticAt 0) hef).2, h L, he _ hf (by simp), hTf, B.sgStar]

namespace TaylorSigmaUniqueness

lemma dblInt_eq (e : PowerSeries ℂ) : C.dblInt e = B.prim (B.prim e) := by
  ext n
  simp only [C.dblInt, B.prim, PowerSeries.coeff_mk]
  rcases n with _ | _ | n
  · simp
  · simp
  · have h1 : ((n : ℂ) + 1 + 1) ≠ 0 := by
      have : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at this
      intro h; apply this; linear_combination h
    have h2 : ((n : ℂ) + 1) ≠ 0 := by
      have : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at this
      exact this
    simp
    field_simp

end TaylorSigmaUniqueness

open TaylorSigmaUniqueness in

theorem taylorSgStar'_of (h : TaylorSgStar) : TaylorSgStar' := by
  intro L
  rw [h L, B.sgStar, B.sigma, C.sgStar, C.lam, dblInt_eq, mul_assoc]
  congr 1
  have h1 : MvPowerSeries.constantCoeff (B.sigS (pSeries L)) = 0 := by
    have : PowerSeries.constantCoeff (B.sigS (pSeries L)) = 0 := by
      rw [B.sigS, map_neg, B.constantCoeff_prim, neg_zero]
    exact this
  have h2 : MvPowerSeries.constantCoeff
      (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) : PowerSeries ℂ) = 0 := by
    have : PowerSeries.constantCoeff
        (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) : PowerSeries ℂ) = 0 := by simp
    exact this
  rw [← B.fExp_add h1 h2, B.sigS, ← neg_add]
  rfl

end Formalism.L2.Th1.F
