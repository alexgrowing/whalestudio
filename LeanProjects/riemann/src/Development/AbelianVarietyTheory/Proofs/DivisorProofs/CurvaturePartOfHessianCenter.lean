import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InSOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralCutoffLogDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPotentialPositiveOnComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularizedMetricLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFormBoundedByLeviStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothBoundKappaStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.FlagPoly

namespace GlobalTheory.RegCurv

theorem smooth_alg : HessSt → CentSt → OnCore fun _ O x P => ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
    ∀ c σ u, ((O.var c).an σ).SmoothOn Set.univ (P.reg c σ u t) := by
  intro hH hC D O x P hcore hN hex
  obtain ⟨C, t₀, -, ht₀, hH⟩ := hH D O x P hcore hN hex
  have hC := hC D O x P hcore hN hex
  refine ⟨t₀, ht₀, fun t ht htt c σ u j => ?_⟩
  have hf : ∀ τ (i : Fin O.N), ((O.var c).an σ).SmoothOn Set.univ (P.regFund c σ τ i t) := by
    intro τ i
    by_cases hi : (i : ℕ) + 1 < O.N
    · exact (hH t ht htt c σ τ i hi).1
    · have hi' : (i : ℕ) + 1 = O.N := by omega
      have := (hC c σ τ i hi').1
      have e : P.regFund c σ τ i t = extBd O.Φ (HeightParts.psi O x c σ τ i) := by
        funext y
        simp only [PolDat.regFund, if_neg hi]
      rw [e]
      exact this
  refine (ContDiffOn.sum (s := Finset.univ) fun τ _ => ContDiffOn.sum (s := Finset.univ) fun i _ =>
    (contDiffOn_const (c := coef u τ i)).mul (hf τ i j)).congr fun v _ => ?_
  rfl

end GlobalTheory.RegCurv

namespace GlobalTheory.RegCurv

theorem curvPart : HessSt → CentSt → OnObj fun _ _ _ T _ _ => ∀ c, GlobalTheory.RegEst.CurvPart (T.F c) := by
  intro hH hC D O hO hN A T H h c
  obtain ⟨x, P, hcore⟩ := hO
  have hex : ∃ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), Nonempty (O.Reads A T H) := ⟨A, T, H, ⟨h⟩⟩
  obtain ⟨t₁, ht₁, hsm₁⟩ := smooth_alg hH hC D O x P hcore hN hex
  obtain ⟨C₂, t₂, hC₂, ht₂, hk⟩ := GlobalTheory.T.regularized_metric_lower_bound hH hC D O x P hcore hN hex
  set I := h.man c with hI
  have hd : (O.var c).dim = Formalism.MainNotions.WeightThresholdDefs.dimY O.Y := by rw [O.dim_eq c]; rfl
  choose K hK hOm using fun a => GlobalTheory.T.kaehler_form_bounded_by_levi I hd a (P.om c (I.ε a)) (P.om_kaehler c _)
  set Km := ∑ a, K a with hKm_def
  have hKm : ∀ a, K a ≤ Km := fun a =>
    Finset.single_le_sum (f := K) (fun b _ => (hK b).le) (Finset.mem_univ a)
  set L₀ := max 1 (-Real.log (min t₁ t₂)) with hL₀
  have hL₀1 : 1 ≤ L₀ := le_max_left _ _
  refine ⟨(L₀ + 1)⁻¹, by positivity, Real.pi / 2 * C₂ * Km, fun C hCC u hu s hs hss l hl a => ?_⟩
  set t := Real.exp (-(s ^ 2)⁻¹) with ht_def
  have hs2 : s ^ 2 ≤ (L₀ + 1)⁻¹ := by
    have h1 : s ≤ 1 := hss.trans (inv_le_one_of_one_le₀ (by linarith))
    nlinarith
  have hl1 : L₀ + 1 ≤ l := by
    rw [hl]
    have := (inv_le_inv₀ (by positivity) (by positivity)).2 hs2
    rwa [inv_inv] at this
  have ht0 : 0 < t := Real.exp_pos _
  have htle : t ≤ min t₁ t₂ := by
    rw [ht_def, ← hl]
    have hm : 0 < min t₁ t₂ := lt_min ht₁ ht₂
    rw [← Real.exp_log hm]
    refine Real.exp_le_exp.2 ?_
    have := le_max_right 1 (-Real.log (min t₁ t₂))
    linarith
  have hlogt : Real.log (1 / t) = l := by
    rw [ht_def, one_div, ← Real.exp_neg, Real.log_exp, neg_neg, hl]
  have hreg : ∀ z, (T.F c).phS u s a z = P.reg c (I.ε a) u t (I.pt a z) / 2 := fun z => by
    rw [(h.an c).phS u s hs a z, hcore.reg_eq]
  have hsm := hsm₁ t ht0 (htle.trans (min_le_left _ _)) c (I.ε a) u
  have hgs : ((O.var c).an (I.ε a)).SmoothOn Set.univ (fun y => P.reg c (I.ε a) u t y / 2) := fun j =>
    (hsm j).div_const 2
  have hF : (T.F c).phS u s a = fun z => (fun y => P.reg c (I.ε a) u t y / 2) (I.pt a z) := funext hreg
  constructor
  · have := GlobalTheory.HodgeChgSmooth.smoothOn_of_manIs I hd a isOpen_univ hgs (f := (T.F c).phS u s a) (fun z _ => hreg z)
    show ((T.M c).A a).SmoothOn Set.univ _
    simpa using this
  · rw [hF]
    have hm0 : ∀ xx, (O.var c).mSmooth (I.ε a) _ (O.met.h0 c (I.ε a) (O.ex xx)) := by
      intro xx
      rw [hcore.h0_eq]
      exact (FlagCpt.smoothOn_met_of_eigMet _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C c) (I.ε a) (x.eigMet _) Set.univ isOpen_univ
        (x.smoothOn_eigMet _) _).2
    refine GlobalTheory.T.potential_smooth_bound_kappa I hd a (fun xx σ' => O.met.h0 c σ' (O.ex xx)) hm0 (fun xx => -u xx.1 xx.2) ((h.an c).th u)
      (T.th_pot c u a) _ hgs _ ?_
    intro ch y hy x' hx' ξ
    obtain ⟨hL0, hLK⟩ := hOm a ch y hy x' hx' ξ
    set L := ch.levi (fun z => (T.M c).Om a |>.φ x' ((I.pt a).symm z)) y ξ with hL
    have hk' := hk t ht0 (htle.trans (min_le_right _ _)) c (I.ε a) u hu ch y hy ξ
    rw [hlogt] at hk'
    have hc2 := hsm.contDiffAt_two isOpen_univ hy trivial
    have e1 : ch.levi (fun y => P.reg c (I.ε a) u t y / 2) y ξ = 1 / 2 * ch.levi (P.reg c (I.ε a) u t) y ξ := by
      rw [← AlgChart.levi_const_mul _ hc2]
      congr 1
      funext z
      ring
    have e2 : ddcForm (P.reg c (I.ε a) u t) ch y ξ = ch.levi (P.reg c (I.ε a) u t) y ξ / Real.pi := rfl
    have e3 : ∑ xx : DV.Rt D.what₂.Tau O.N, -u xx.1 xx.2 * (Real.pi / 2 * curvMet (O.met.h0 c (I.ε a) (O.ex xx)) ch y ξ) =
        Real.pi / 2 * thW (refMet x O.Φ) c (I.ε a) u ch y ξ := by
      simp only [thW, ← hcore.h0_eq, Finset.mul_sum, mul_neg]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun xx _ => ?_
      show _ = -(Real.pi / 2 * (u xx.1 xx.2 * curvMet (O.met.h0 c (I.ε a) (O.ex xx)) ch y ξ))
      ring
    rw [e1, e3]
    have hq : 0 ≤ Real.log l / l := div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
    have hpi := Real.pi_pos
    set q := Real.log l / l
    have hnu : 0 ≤ ‖u‖ := norm_nonneg _
    have hB : C₂ * ‖u‖ * q * P.om c (I.ε a) ch y ξ ≤ C₂ * ‖u‖ * q * (K a * L) :=
      mul_le_mul_of_nonneg_left hLK (by positivity)
    have hCK : Real.pi / 2 * C₂ * K a ≤ C := le_trans (by gcongr; exact hKm a) hCC
    have hX : Real.pi / 2 * C₂ * K a * (‖u‖ * q * L) ≤ C * (‖u‖ * q * L) :=
      mul_le_mul_of_nonneg_right hCK (by positivity)
    have hk2 : -(C₂ * ‖u‖ * q * P.om c (I.ε a) ch y ξ) ≤ thW (refMet x O.Φ) c (I.ε a) u ch y ξ +
        ch.levi (P.reg c (I.ε a) u t) y ξ / Real.pi := hk'
    have hk3 : -(Real.pi * (C₂ * ‖u‖ * q * P.om c (I.ε a) ch y ξ)) ≤
        Real.pi * thW (refMet x O.Φ) c (I.ε a) u ch y ξ + ch.levi (P.reg c (I.ε a) u t) y ξ := by
      have := mul_le_mul_of_nonneg_left hk2 hpi.le
      rw [mul_add, mul_div_cancel₀ _ hpi.ne'] at this
      linarith
    nlinarith

end GlobalTheory.RegCurv
