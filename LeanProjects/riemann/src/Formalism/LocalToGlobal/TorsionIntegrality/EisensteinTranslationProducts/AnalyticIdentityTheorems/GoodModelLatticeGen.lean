import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorSigma
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaScale
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassNumeratorDenominator

noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (wpNum wpDen uSer IsGoodModel)

namespace Formalism.L2.Th1.F

open PowerSeries TaylorWp

namespace USer

def num (L : PeriodPair) (z : ℂ) : ℂ := 1 + z ^ 2 * L.weierstrassPExcept 0 z

def den (L : PeriodPair) (z : ℂ) : ℂ := 1 + -(1 / 2) * z ^ 3 * deriv (L.weierstrassPExcept 0) z

theorem T_num (hr : TaylorRing) (L : PeriodPair) : T (num L) (1 + X ^ 2 * pSeries L) := by
  obtain ⟨hadd, hC, hX, -⟩ := hr
  have hP := TaylorSigmaUniqueness.analyticAt_pExcept L
  have hz : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hz2 : AnalyticAt ℂ (fun z : ℂ => z * z) 0 := hz.mul hz
  have hprod : AnalyticAt ℂ (fun z => z * z * L.weierstrassPExcept 0 z) 0 := hz2.mul hP
  have e : num L = fun z => (fun _ : ℂ => (1 : ℂ)) z + (fun z => z * z * L.weierstrassPExcept 0 z) z := by
    funext z
    simp only [num]
    ring
  refine ⟨by rw [e]; exact analyticAt_const.add hprod, ?_⟩
  have h1 : taylor0 (num L) = taylor0 (fun _ : ℂ => (1 : ℂ)) +
      taylor0 (fun z => z * z * L.weierstrassPExcept 0 z) := by
    rw [e]
    exact (hadd _ _ analyticAt_const hprod).1
  have h2 : taylor0 (fun z => z * z * L.weierstrassPExcept 0 z) =
      taylor0 (fun z : ℂ => z * z) * taylor0 (L.weierstrassPExcept 0) :=
    (hadd (fun z : ℂ => z * z) (L.weierstrassPExcept 0) hz2 hP).2
  have h3 : taylor0 (fun z : ℂ => z * z) = taylor0 (fun z : ℂ => z) * taylor0 (fun z : ℂ => z) :=
    (hadd (fun z : ℂ => z) (fun z : ℂ => z) hz hz).2
  rw [h1, h2, h3, hC, hX, map_one, sq]
  rfl

theorem T_den (hr : TaylorRing) (hd : TaylorDeriv) (L : PeriodPair) :
    T (den L) (1 - C (1 / 2 : ℂ) * X ^ 3 * derivative ℂ (pSeries L)) := by
  obtain ⟨hadd, hC, hX, -⟩ := hr
  have hP := TaylorSigmaUniqueness.analyticAt_pExcept L
  have hPd : AnalyticAt ℂ (deriv (L.weierstrassPExcept 0)) 0 := hP.deriv
  have hz : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hz2 : AnalyticAt ℂ (fun z : ℂ => z * z) 0 := hz.mul hz
  have hz3 : AnalyticAt ℂ (fun z : ℂ => z * z * z) 0 := hz2.mul hz
  have hc3 : AnalyticAt ℂ (fun z : ℂ => -(1 / 2 : ℂ) * (z * z * z)) 0 := analyticAt_const.mul hz3
  have hprod : AnalyticAt ℂ (fun z => -(1 / 2 : ℂ) * (z * z * z) * deriv (L.weierstrassPExcept 0) z) 0 :=
    hc3.mul hPd
  have e : den L = fun z => (fun _ : ℂ => (1 : ℂ)) z +
      (fun z => -(1 / 2 : ℂ) * (z * z * z) * deriv (L.weierstrassPExcept 0) z) z := by
    funext z
    simp only [den]
    ring
  refine ⟨by rw [e]; exact analyticAt_const.add hprod, ?_⟩
  have h1 : taylor0 (den L) = taylor0 (fun _ : ℂ => (1 : ℂ)) +
      taylor0 (fun z => -(1 / 2 : ℂ) * (z * z * z) * deriv (L.weierstrassPExcept 0) z) := by
    rw [e]
    exact (hadd _ _ analyticAt_const hprod).1
  have h2 : taylor0 (fun z => -(1 / 2 : ℂ) * (z * z * z) * deriv (L.weierstrassPExcept 0) z) =
      taylor0 (fun z : ℂ => -(1 / 2 : ℂ) * (z * z * z)) * taylor0 (deriv (L.weierstrassPExcept 0)) :=
    (hadd (fun z : ℂ => -(1 / 2 : ℂ) * (z * z * z)) (deriv (L.weierstrassPExcept 0)) hc3 hPd).2
  have h3 : taylor0 (fun z : ℂ => -(1 / 2 : ℂ) * (z * z * z)) =
      taylor0 (fun _ : ℂ => -(1 / 2 : ℂ)) * taylor0 (fun z : ℂ => z * z * z) :=
    (hadd (fun _ : ℂ => -(1 / 2 : ℂ)) (fun z : ℂ => z * z * z) analyticAt_const hz3).2
  have h4 : taylor0 (fun z : ℂ => z * z * z) = taylor0 (fun z : ℂ => z * z) * taylor0 (fun z : ℂ => z) :=
    (hadd (fun z : ℂ => z * z) (fun z : ℂ => z) hz2 hz).2
  have h5 : taylor0 (fun z : ℂ => z * z) = taylor0 (fun z : ℂ => z) * taylor0 (fun z : ℂ => z) :=
    (hadd (fun z : ℂ => z) (fun z : ℂ => z) hz hz).2
  rw [h1, h2, h3, h4, h5, hC, hC, hX, hd.1 _ hP, map_one, map_neg]
  show _ = 1 - PowerSeries.C (1 / 2 : ℂ) * PowerSeries.X ^ 3 * PowerSeries.derivative ℂ (taylor0 (L.weierstrassPExcept 0))
  ring

theorem den_zero (L : PeriodPair) : den L 0 = 1 := by
  simp [den]

theorem u_eventuallyEq (L : PeriodPair) :
    (fun z => -2 * L.weierstrassP z / L.derivWeierstrassP z)
      =ᶠ[nhds 0] fun z => z * num L z / den L z := by
  have hPl : L.weierstrassP = fun w => L.weierstrassPExcept 0 w + 1 / w ^ 2 := funext fun w => by
    have := Formalism.L2.Th1.F.IsogenyPAux.P_local L 0 (zero_mem _) w
    simpa using this
  have hev := (TaylorSigmaUniqueness.analyticAt_pExcept L).eventually_analyticAt
  filter_upwards [hev] with z hz
  by_cases hz0 : z = 0
  · subst hz0
    simp [hPl, PeriodPair.weierstrassPExcept_zero]
  · have hd : L.derivWeierstrassP z = deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 := by
      rw [← L.deriv_weierstrassP, hPl]
      have h1 : HasDerivAt (fun w => L.weierstrassPExcept 0 w) (deriv (L.weierstrassPExcept 0) z) z :=
        hz.differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun w : ℂ => 1 / w ^ 2) (-2 / z ^ 3) z := by
        have h3 := (hasDerivAt_pow 2 z).inv (pow_ne_zero 2 hz0)
        have e : (fun w : ℂ => 1 / w ^ 2) = fun w => (w ^ 2)⁻¹ := funext fun w => one_div _
        rw [e]
        refine h3.congr_deriv ?_
        have e2 : (2 : ℕ) - 1 = 1 := rfl
        rw [e2]
        push_cast
        field_simp
      have h4 := (h1.add h2).deriv
      rw [show (fun w => L.weierstrassPExcept 0 w + 1 / w ^ 2) =
        ((fun w => L.weierstrassPExcept 0 w) + fun w : ℂ => 1 / w ^ 2) from rfl, h4]
      ring
    rw [hd, hPl]
    simp only [num, den]
    by_cases hD : (1 + -(1 / 2 : ℂ) * z ^ 3 * deriv (L.weierstrassPExcept 0) z) = 0
    · have hD' : deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 = 0 := by
        have e : deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 =
            (-2 / z ^ 3) * (1 + -(1 / 2 : ℂ) * z ^ 3 * deriv (L.weierstrassPExcept 0) z) := by
          field_simp
          ring
        rw [e, hD, mul_zero]
      rw [hD, hD', div_zero, div_zero]
    · have hD' : deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 ≠ 0 := by
        intro h
        apply hD
        have e : 1 + -(1 / 2 : ℂ) * z ^ 3 * deriv (L.weierstrassPExcept 0) z =
            (-(z ^ 3) / 2) * (deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3) := by
          field_simp
          ring
        rw [e, h, mul_zero]
      rw [div_eq_div_iff hD' hD]
      field_simp
      ring

theorem uSerLattice_gen (hr : TaylorRing) (hd : TaylorDeriv) (hp : POfLattice) (hn : WpNumDen) :
    USerLattice := by
  intro L
  have hN := T_num hr L
  have hD := T_den hr hd L
  have hden0 : den L 0 = 1 := den_zero L
  have hev := u_eventuallyEq L
  have hne : den L 0 ≠ 0 := by rw [hden0]; exact one_ne_zero
  have hzN : AnalyticAt ℂ (fun z => z * num L z) 0 := analyticAt_id.mul hN.1
  have hinv : AnalyticAt ℂ (fun z => (den L z)⁻¹) 0 := hD.1.inv hne
  have hquot : AnalyticAt ℂ (fun z => z * num L z / den L z) 0 := hzN.div hD.1 hne
  refine ⟨hquot.congr hev.symm, ?_⟩
  have h0 : taylor0 (fun z => -2 * L.weierstrassP z / L.derivWeierstrassP z) =
      taylor0 (fun z => z * num L z / den L z) := hr.2.2.2 _ _ hev
  have h1 : taylor0 (fun z => z * num L z / den L z) =
      taylor0 (fun z => z * num L z) * taylor0 (fun z => (den L z)⁻¹) := by
    have e : (fun z => z * num L z / den L z) = fun z => (z * num L z) * (den L z)⁻¹ := by
      funext z
      rw [div_eq_mul_inv]
    rw [e]
    exact (hr.1 (fun z => z * num L z) (fun z => (den L z)⁻¹) hzN hinv).2
  have h2 : taylor0 (fun z => z * num L z) = taylor0 (fun z : ℂ => z) * taylor0 (num L) :=
    (hr.1 (fun z : ℂ => z) (num L) analyticAt_id hN.1).2
  have hmul : taylor0 (fun z => (den L z)⁻¹) * taylor0 (den L) = 1 := by
    have e1 : taylor0 (fun z => (den L z)⁻¹ * den L z) =
        taylor0 (fun z => (den L z)⁻¹) * taylor0 (den L) :=
      (hr.1 (fun z => (den L z)⁻¹) (den L) hinv hD.1).2
    have hc := hD.1.continuousAt.eventually_ne hne
    have e2 : taylor0 (fun z => (den L z)⁻¹ * den L z) = taylor0 (fun _ : ℂ => (1 : ℂ)) := by
      refine hr.2.2.2 _ _ ?_
      filter_upwards [hc] with z hz
      exact inv_mul_cancel₀ hz
    rw [← e1, e2, hr.2.1, map_one]
  have hc0 : PowerSeries.constantCoeff (taylor0 (den L)) ≠ 0 := by
    rw [hD.2]
    simp
  have hinv2 : taylor0 (fun z => (den L z)⁻¹) = (taylor0 (den L))⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one hc0).mpr hmul
  rw [h0, h1, h2, hinv2, hr.2.2.1, hN.2, hD.2]
  unfold uSer
  rw [(hn ℂ L.g₂ L.g₃).1, (hn ℂ L.g₂ L.g₃).2, ← hp L]

theorem goodModelLattice_gen (hh : Homogeneity) (hp : POfLattice) (hm : SeriesMap) (hs : TaylorSigma)
    (hst : TaylorSgStar) (hu : USerLattice) : GoodModelLattice := by
  intro l _ L ι g2 g3 hG
  obtain ⟨-, -, -, -, -, lam, hlam, h2, h3⟩ := hG
  obtain ⟨c, hιc⟩ : ∃ c : ℂ, ι c = lam⁻¹ := ⟨ι.symm lam⁻¹, ι.apply_symm_apply _⟩
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hιc
    exact inv_ne_zero hlam hιc.symm
  refine ⟨c, hc, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := hh L c hc
  have e2 : ι (scalePair L c hc).g₂ = g2 := by
    rw [hg2, map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv]
    exact h2.symm
  have e3 : ι (scalePair L c hc).g₃ = g3 := by
    rw [hg3, map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv]
    exact h3.symm
  obtain ⟨-, -, hMp, hMu, hMs, hMst⟩ := hm ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (scalePair L c hc).g₂
    (scalePair L c hc).g₃ (s2 (scalePair L c hc)) (pSeries (scalePair L c hc))
  have e4 : PowerSeries.map (ι : ℂ →+* ℂ_[l]) (pSeries (scalePair L c hc)) = pOf g2 g3 := by
    rw [hp (scalePair L c hc), hMp]
    exact congrArg₂ pOf e2 e3
  refine ⟨e2.symm, e3.symm, e4, ?_, ?_, ?_⟩
  · rw [hs (scalePair L c hc), hMs, e4]
  · rw [hst (scalePair L c hc), hMst, e4]
    rfl
  · rw [(hu (scalePair L c hc)).2, hMu]
    exact congrArg₂ uSer e2 e3

end USer

theorem uSerLattice_of (hp : POfLattice) (hn : WpNumDen) : USerLattice := USer.uSerLattice_gen taylor_ring taylor_deriv hp hn

theorem goodModelLattice_of (hp : POfLattice) (hn : WpNumDen) : GoodModelLattice := USer.goodModelLattice_gen homogeneity_thm hp series_map
    (taylorSigma_of taylor_ring taylor_deriv)
    (taylorSgStar_of (taylorSigma_of taylor_ring taylor_deriv) taylor_ring taylor_exp
      sigmaEntire)
    (uSerLattice_of hp hn)

theorem u_series_lattice : USerLattice := uSerLattice_of weierstrass_p_of_lattice weierstrass_numerator_denominator

theorem good_model_lattice : GoodModelLattice := goodModelLattice_of weierstrass_p_of_lattice weierstrass_numerator_denominator

end Formalism.L2.Th1.F
