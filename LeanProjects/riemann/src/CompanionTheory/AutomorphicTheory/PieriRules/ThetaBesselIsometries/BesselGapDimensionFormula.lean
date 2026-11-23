import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.WeilFormulaIntegrableComplexImports
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapVanishingStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.GapCoefficientBoundStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.GapCoefficientBoundDualStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselNorm

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

theorem fdegHC_pos {n : ℕ} (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    0 < Formalism.QuantumDeterminants.fdegHC lam := by
  unfold Formalism.QuantumDeterminants.fdegHC
  apply div_pos
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hab.ne (hlam h))
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    exact sub_pos.mpr (Nat.cast_lt.mpr (Finset.mem_filter.mp hb).2)

theorem quot_ae {k r : ℕ} {μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μS]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) (hG : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r)
    (hS : ∀ᵐ x ∂μS, Matrix.of x ∈ GG k r) (h0 : μS ≠ 0) : ∀ᵐ x ∂νq, Matrix.of x ∈ GG k r := by
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hm : MeasurableSet {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ GG k r} :=
    (isClosed_UH.preimage hof).measurableSet
  set f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := ({y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ GG k r}ᶜ).indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hm.compl
  have h1 : ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (mulMt s x) ∂μS ∂νq := hq f hfm
  have h2 : ∫⁻ x, f x ∂μG = 0 := by
    rw [hf, lintegral_indicator_one hm.compl]; exact hG
  have h3 : Measurable (fun x => ∫⁻ s, f (mulMt s x) ∂μS) :=
    (hfm.comp measurable_mulMt).lintegral_prod_left'
  rw [h2, eq_comm, lintegral_eq_zero_iff h3] at h1
  filter_upwards [h1] with x hx
  by_contra hxG
  have h4 : ∫⁻ s, f (mulMt s x) ∂μS = ∫⁻ _s, 1 ∂μS := by
    apply lintegral_congr_ae
    filter_upwards [hS] with s hs
    have : mulMt s x ∈ ({y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ GG k r}ᶜ) := by
      intro hsx
      apply hxG
      have hsx' : Matrix.of s * Matrix.of x ∈ GG k r := hsx
      have := DDSmoothness.uh_mul (uh_inv hs).1 hsx'
      rwa [← Matrix.mul_assoc, (uh_inv hs).2.2, Matrix.one_mul] at this
    rw [hf, Set.indicator_of_mem this]; rfl
  rw [h4] at hx
  simp only [lintegral_const, one_mul, Pi.zero_apply, Measure.measure_univ_eq_zero] at hx
  exact h0 hx

theorem piInv_contOn {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (ξ : Wp) :
    ContinuousOn (fun p1 : Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p1)⁻¹ ξ)
      {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} := by
  have hm : Continuous (fun p1 : Formalism.QuantumDeterminants.Mt k r =>
      Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r) :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  have hmaps : Set.MapsTo (fun p1 : Formalism.QuantumDeterminants.Mt k r =>
      Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r)
      {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} (Formalism.QuantumDeterminants.UWset k r z) := by
    intro p1 hp1
    have e : (Matrix.of p1 : Mx k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r :=
      PI.HwUniqW.inv_eq_UH hp1.1
    show Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r ∈ Formalism.QuantumDeterminants.UWset k r z
    rw [← e]; exact (uw_inv hp1).1
  refine ((piW_cont hT hπ ξ).comp hm.continuousOn hmaps).congr ?_
  intro p1 hp1
  have e : (Matrix.of p1 : Mx k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r :=
    PI.HwUniqW.inv_eq_UH hp1.1
  simp only [Function.comp]
  rw [e]

def kern {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (v w : R.H) (ξ : Wp)
    (y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) : ℂ :=
  ⟪v, R.σ (Matrix.of y.1) w⟫_ℂ * star ⟪v, R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w⟫_ℂ *
    (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of y.2.2) * ⟪π (Matrix.of y.2.1)⁻¹ ξ, ξ⟫_ℂ)

def good (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) :=
  {y | Matrix.of y.1 ∈ GG k r ∧ Matrix.of y.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of y.2.2 ∈ GG k r}

theorem good_meas (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : MeasurableSet (good k r z) := by
  have h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r)) := continuous_fst.comp continuous_snd
  have h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.2 : Mx k r)) := continuous_snd.comp continuous_snd
  have h3 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.1 : Mx k r)) := continuous_fst
  exact ((isClosed_UH.preimage h3).inter (((isClosed_UW z).preimage h1).inter
    (isClosed_UH.preimage h2))).measurableSet

theorem kern_meas {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (v w : R.H) (ξ : Wp)
    (hc : ContinuousOn (fun g => R.σ g w) (GG k r)) :
    Measurable ((good k r z).indicator (kern R z π v w ξ)) := by
  classical
  have h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r)) := continuous_fst.comp continuous_snd
  have h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.2 : Mx k r)) := continuous_snd.comp continuous_snd
  have h3 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.1 : Mx k r)) := continuous_fst
  have a1 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      R.σ (Matrix.of y.1) w) (good k r z) := hc.comp h3.continuousOn (fun y hy => hy.1)
  have a2 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w) (good k r z) :=
    hc.comp ((h1.matrix_mul h2).matrix_mul h3).continuousOn
      (fun y hy => DDSmoothness.uh_mul (DDSmoothness.uh_mul hy.2.1.1 hy.2.2) hy.1)
  have a3 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      π (Matrix.of y.2.1)⁻¹ ξ) (good k r z) :=
    (piInv_contOn hT hπ ξ).comp (continuous_fst.comp continuous_snd).continuousOn (fun y hy => hy.2.1)
  have hK : ContinuousOn (kern R z π v w ξ) (good k r z) :=
    ((continuousOn_const.inner a1).mul (continuous_star.comp_continuousOn (continuousOn_const.inner a2))).mul
      (((psi_cont z _).comp h2).continuousOn.mul (a3.inner continuousOn_const))
  have := ContinuousOn.measurable_piecewise hK (continuousOn_const (c := (0 : ℂ))) (good_meas k r z)
  rw [← Set.piecewise_eq_indicator]
  exact this

set_option maxHeartbeats 1600000 in

theorem norm_integral (hy : HypsG) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ)
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (hR : R.IsDG ε mu) (hgap : Formalism.QuantumDeterminants.GapAtLeast ε mu h)
    (hok : GapOK k r h) (hS : SideG k r z π u μW μN μG νq) (d : ℝ)
    (hSd : ∀ v w v' w' : R.H, ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG =
      ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    (v : R.H) (hv : v ∈ R.TK) (ξ : Wp) (w : R.H) (hw : w ∈ R.sm) :
    Integrable (fun x : Formalism.QuantumDeterminants.Mt k r =>
      ‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w) v ξ‖ ^ 2) νq ∧
    ((∫ x : Formalism.QuantumDeterminants.Mt k r, ‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w) v ξ‖ ^ 2 ∂νq : ℝ) : ℂ) =
      ((‖w‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) * ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ, ξ⟫_ℂ := by
  obtain ⟨hmul, hone, hun, hsm, hTK, -, -, -, hcont⟩ := GlobalTheory.rep_basic_of_isDS hy.1.2.2.1 k r ε mu R hR
  have hfub := GlobalTheory.T.integrable_coefficient_mul_star_translate hy k r ε mu h R Wp z π u μW μN μG νq hR hgap hok hS v hv w hw
  have hpt := GlobalTheory.T.coefficient_psi_pairing_eq_iterated_integral hy k r ε mu h R Wp z π u μW μN μG νq hR hgap hok hS v hv
  have hconv := (GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hy k r ε mu h R Wp z π u μW μN μG νq hR hgap hok hS v hv).1 v (hTK v hv)
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hWh, hNh, hGh, hq⟩ := hS
  have := hWh.1; have := hNh.1; have := hGh.1
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ GG k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and
      (Measure.quasiMeasurePreserving_snd.ae (hNae.mono fun _ hx => hx.1))
  have hQae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ good k r z :=
    (Measure.quasiMeasurePreserving_fst.ae hGae).and (Measure.quasiMeasurePreserving_snd.ae hPae)
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hSeq : muSof μW μN = (μW.prod μN).map (fun p => mulMt p.1 p.2) := rfl
  have hsf : SFinite (muSof μW μN) := by rw [hSeq]; infer_instance
  have hSae : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ GG k r := by
    rw [hSeq]
    refine (ae_map_iff measurable_mulMt.aemeasurable (isClosed_UH.preimage hof).measurableSet).2 ?_
    filter_upwards [hPae] with p hp
    exact DDSmoothness.uh_mul hp.1.1 hp.2
  have hS0 : muSof μW μN ≠ 0 := by
    rw [hSeq, Ne, Measure.map_eq_zero_iff measurable_mulMt.aemeasurable]
    intro h0
    have h1 : (μW.prod μN) (Set.univ ×ˢ Set.univ) = 0 := by rw [h0]; rfl
    rw [Measure.prod_prod, mul_eq_zero, Measure.measure_univ_eq_zero, Measure.measure_univ_eq_zero] at h1
    exact h1.elim hWh.2.1 hNh.2.1
  have hνae := quot_ae hq hGae hSae hS0
  set F := (good k r z).indicator (kern R z π v w ξ) with hF
  have hFm : Measurable F := kern_meas R hT hπ v w ξ (hcont w)
  have hFK : F =ᵐ[μG.prod (μW.prod μN)] kern R z π v w ξ := by
    filter_upwards [hQae] with q hq
    rw [hF, Set.indicator_of_mem hq]
  have hFi : Integrable F (μG.prod (μW.prod μN)) := by
    refine Integrable.mono' (hfub.norm.mul_const (‖ξ‖ * ‖ξ‖)) hFm.aestronglyMeasurable ?_
    filter_upwards [hQae] with q hq
    rw [hF, Set.indicator_of_mem hq, kern, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_mul, psi_norm, one_mul]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [piW_unitary hT hπ _ (uw_inv hq.2.1).1 ξ]
  set f : Formalism.QuantumDeterminants.Mt k r → ℂ := fun x => ∫ q, F (x, q) ∂(μW.prod μN) with hf
  have hfm : Measurable f := (hFm.stronglyMeasurable.integral_prod_right' (ν := μW.prod μN)).measurable
  have hfi : Integrable f μG := hFi.integral_prod_left
  obtain ⟨-, hgi, hge⟩ := GlobalTheory.T.weil_formula_integrable_complex k r μG (muSof μW μN) νq f hq hfm hfi

  have hg : ∀ᵐ x ∂νq, ∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muSof μW μN) =
      ((‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w) v ξ‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [hνae] with x hx
    rw [hpt _ (hsm _ hx w hw) ξ, hSeq]
    have hm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => f (mulMt s x)) :=
      hfm.comp (measurable_mulMt.comp (measurable_id.prodMk measurable_const))
    refine (integral_map measurable_mulMt.aemeasurable hm.aestronglyMeasurable).trans ?_
    apply integral_congr_ae
    filter_upwards [hPae] with p hp
    apply integral_congr_ae
    filter_upwards [hPae] with q hq'
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r := DDSmoothness.uh_mul hp.1.1 hp.2
    have ht : Matrix.of q.1 * Matrix.of q.2 ∈ GG k r := DDSmoothness.uh_mul hq'.1.1 hq'.2
    have hgood : (mulMt (mulMt p.1 p.2) x, q) ∈ good k r z := ⟨DDSmoothness.uh_mul hs hx, hq'.1, hq'.2⟩
    rw [hF, Set.indicator_of_mem hgood, ← hmul _ hs _ hx, ← hmul _ (DDSmoothness.uh_mul ht hs) _ hx,
      Matrix.mul_assoc (Matrix.of q.1 * Matrix.of q.2)]
    rfl

  have hI : ∫ x, f x ∂μG = ((‖w‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) * ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ, ξ⟫_ℂ := by
    have e1 : ∫ x, f x ∂μG = ∫ q, ∫ x, F (x, q) ∂μG ∂(μW.prod μN) :=
      integral_integral_swap (f := fun x q => F (x, q)) hFi
    have e2 : be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ = ∫ p, beInt z Formalism.QuantumDeterminants.cStd π R.σ v v p ξ ∂(μW.prod μN) :=
      ContinuousLinearMap.integral_apply hconv ξ
    have e3 : ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ, ξ⟫_ℂ =
        ∫ p, ⟪beInt z Formalism.QuantumDeterminants.cStd π R.σ v v p ξ, ξ⟫_ℂ ∂(μW.prod μN) := by
      rw [← inner_conj_symm, e2, ← integral_inner (hconv.apply_continuousLinearMap ξ), ← integral_conj]
      simp only [inner_conj_symm]
    rw [e1, e3, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hPae] with q hq'
    have ht : Matrix.of q.1 * Matrix.of q.2 ∈ GG k r := DDSmoothness.uh_mul hq'.1.1 hq'.2
    have e4 : ∀ᵐ x ∂μG, F (x, q) = ⟪v, R.σ (Matrix.of x) w⟫_ℂ *
        star ⟪R.σ (Matrix.of q.1 * Matrix.of q.2)⁻¹ v, R.σ (Matrix.of x) w⟫_ℂ *
        (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of q.2) * ⟪π (Matrix.of q.1)⁻¹ ξ, ξ⟫_ℂ) := by
      filter_upwards [hGae] with x hx
      have hgood : (x, q) ∈ good k r z := ⟨hx, hq'.1, hq'.2⟩
      rw [hF, Set.indicator_of_mem hgood, kern, hmul _ ht _ hx, sigma_inner hR.2 ht]
    rw [integral_congr_ae e4, integral_mul_const, hSd, ← inner_conj_symm v, ← sigma_inner hR.2 ht,
      inner_self_eq_norm_sq_to_K]
    simp only [beInt, ContinuousLinearMap.smul_apply, inner_smul_left, map_mul, RCLike.star_def,
      Complex.conj_conj]
    push_cast
    simp only [Complex.coe_algebraMap]
    ring
  have hgi' := hgi.congr hg
  refine ⟨hgi'.re.congr (Filter.Eventually.of_forall fun x => Complex.ofReal_re _), ?_⟩
  rw [← hI, hge, integral_congr_ae hg, integral_complex_ofReal]

theorem norm_identity : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ dd : ℝ, (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) → ∀ v ∈ R.TK, ∀ ξ : Wp, (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).re ∧ 0 < dd ∧ ∀ w ∈ R.sm, PI.BesselPeriodGGP.l2SG νq (fun g => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ g w) v ξ) = ENNReal.ofReal (‖w‖ ^ 2 * (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).re / dd) := by
  intro hy k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hR hgap hok hS dd hdd v hv ξ
  obtain ⟨-, -, -, -, hTK, -, hKT, ⟨w0, hw0, hw0K, -⟩, -⟩ := GlobalTheory.rep_basic_of_isDS hy.1.2.2.1 k r ε mu R hR
  obtain ⟨c, hc, hSch⟩ := GlobalTheory.BesselDegree.schur_fdeg hy k r ε μG hS.2.2.2.2.2.2.1
  obtain ⟨hdeg, hSd⟩ := hSch mu R hR
  have hw0ne : w0 ≠ 0 := by intro h0; rw [h0, norm_zero] at hw0; exact zero_ne_one hw0
  have hd : c * Formalism.QuantumDeterminants.fdegHC mu = dd := by rw [← hdeg w0 hw0ne, hdd w0 hw0ne]
  have hpos : 0 < dd := hd ▸ mul_pos hc (fdegHC_pos mu hR.1.1.injective)
  rw [hd] at hSd
  have key := fun w hw => norm_integral hy k r ε mu h R Wp z π u μW μN μG νq hR hgap hok hS dd
    (fun a b a' b' => (hSd a b a' b').2) v hv ξ w hw
  set β := ⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ with hβ
  have hconj : ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ, ξ⟫_ℂ = starRingEnd ℂ β := by
    rw [hβ, inner_conj_symm]
  have hre : ∀ w ∈ R.sm,
      ∫ x : Formalism.QuantumDeterminants.Mt k r, ‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w) v ξ‖ ^ 2 ∂νq =
        ‖w‖ ^ 2 * β.re / dd := by
    intro w hw
    have := congrArg Complex.re (key w hw).2
    rw [hconj, ← Complex.ofReal_div, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.conj_re] at this
    rw [this]; ring
  have hw0s : w0 ∈ R.sm := hTK w0 (hKT w0 hw0K)
  refine ⟨?_, ?_, hpos, fun w hw => ?_⟩
  · have := congrArg Complex.im (key w0 hw0s).2
    rw [hconj, ← Complex.ofReal_div, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.conj_im, hw0] at this
    have h1 : (1 : ℝ) ^ 2 / dd ≠ 0 := by positivity
    have := (mul_eq_zero.1 this.symm).resolve_left h1
    linarith
  · have h1 := hre w0 hw0s
    have h2 : 0 ≤ ∫ x : Formalism.QuantumDeterminants.Mt k r,
        ‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w0) v ξ‖ ^ 2 ∂νq :=
      integral_nonneg fun x => by positivity
    rw [h1, hw0, one_pow, one_mul] at h2
    by_contra hneg
    exact absurd h2 (not_le.2 (div_neg_of_neg_of_pos (not_le.1 hneg) hpos))
  · rw [← hre w hw, ofReal_integral_eq_lintegral_ofReal (key w hw).1
      (Filter.Eventually.of_forall fun x => by positivity)]
    unfold PI.BesselPeriodGGP.l2SG
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl

end GlobalTheory.BesselNorm
