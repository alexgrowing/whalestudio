import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSStatements
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Weil

variable {k r : ℕ}

def psiMap (q : Mt k r × (Mt k r × Mt k r)) : Mt k r := fun i j => (sM q.2 * Matrix.of q.1) i j

theorem continuous_psiMap : Continuous (psiMap (k := k) (r := r)) := by
  have hc : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (sM q.2 * Matrix.of q.1 : Mx k r) :=
    ((PI.WUN.continuous_of.comp (continuous_fst.comp continuous_snd)).matrix_mul
      (PI.WUN.continuous_of.comp (continuous_snd.comp continuous_snd))).matrix_mul
      (PI.WUN.continuous_of.comp continuous_fst)
  exact continuous_pi fun i => continuous_pi fun j => hc.matrix_elem i j

theorem measurable_psiMap : Measurable (psiMap (k := k) (r := r)) := continuous_psiMap.measurable

theorem continuous_mulT : Continuous fun q : Mt k r × Mt k r => (fun i j => (Matrix.of q.2 * Matrix.of q.1) i j : Mt k r) := by
  have hc : Continuous fun q : Mt k r × Mt k r => (Matrix.of q.2 * Matrix.of q.1 : Mx k r) :=
    (PI.WUN.continuous_of.comp continuous_snd).matrix_mul (PI.WUN.continuous_of.comp continuous_fst)
  exact continuous_pi fun i => continuous_pi fun j => hc.matrix_elem i j

theorem muS_ne_zero {μG μS ν : Measure (Mt k r)} (hG0 : μG ≠ 0) (hq : IsQuotMeas μG μS ν) : μS ≠ 0 := by
  intro h0
  subst h0
  apply hG0
  have h1 := hq (fun _ => 1) measurable_const
  simpa using h1

theorem sfinite_quot {μG μS ν : Measure (Mt k r)} [SigmaFinite μG] [SFinite μS] (hG0 : μG ≠ 0)
    (hq : IsQuotMeas μG μS ν) : SFinite ν := by
  have hS0 := muS_ne_zero hG0 hq
  obtain ⟨f, hfpos, hfm, hfint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  set F : Mt k r → ENNReal := fun x => (f x : ENNReal) with hFdef
  have hFm : Measurable F := hfm.coe_nnreal_ennreal
  have hmul : ∀ x : Mt k r, Measurable fun s : Mt k r => (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) :=
    fun x => (continuous_mulT.comp (Continuous.prodMk_right x)).measurable
  set h : Mt k r → ENNReal := fun x => ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS with hdef
  have hhm : Measurable h := (hFm.comp continuous_mulT.measurable).lintegral_prod_right'
  have hint : ∫⁻ x, h x ∂ν < ⊤ := by
    rw [hdef, ← hq F hFm]
    exact hfint.trans ENNReal.one_lt_top
  have hpos : ∀ x, h x ≠ 0 := by
    intro x hx
    have hx' := (lintegral_eq_zero_iff (hFm.comp (hmul x))).1 hx
    have hfalse : ∀ᵐ s ∂μS, False := hx'.mono fun s hs => by
      simp only [Function.comp_apply, Pi.zero_apply, hFdef, ENNReal.coe_eq_zero] at hs
      exact (hfpos _).ne' hs
    exact hS0 (by simpa using ae_iff.1 hfalse)
  have hfin : IsFiniteMeasure (ν.withDensity h) := isFiniteMeasure_withDensity hint.ne
  have heq : ν = (ν.withDensity h).withDensity h⁻¹ := by
    rw [← withDensity_mul ν hhm hhm.inv]
    conv_lhs => rw [← withDensity_one (μ := ν)]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_lt_top hhm hint.ne] with x hx
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
    exact (ENNReal.mul_inv_cancel (hpos x) hx.ne).symm
  rw [heq]
  infer_instance

theorem quot_map {μG μW μN ν : Measure (Mt k r)} [SFinite μW] [SFinite μN] [SFinite ν]
    (hq : IsQuotMeas μG (muSof μW μN) ν) : μG = (ν.prod (μW.prod μN)).map psiMap := by
  ext A hA
  have hf : Measurable (A.indicator (1 : Mt k r → ENNReal)) := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA, hq _ hf,
    lintegral_map hf measurable_psiMap,
    lintegral_prod (fun w => A.indicator 1 (psiMap w)) (hf.comp measurable_psiMap).aemeasurable]
  refine lintegral_congr fun x => ?_
  have hf1 : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ENNReal)
      (fun i j => (Matrix.of s * Matrix.of x) i j) :=
    hf.comp (continuous_mulT.comp (Continuous.prodMk_right x)).measurable
  have hg1 : Measurable fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r) :=
    (continuous_mulT.comp continuous_swap).measurable
  rw [muSof, lintegral_map hf1 hg1]
  rfl

theorem gHyp_sfinite {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {μW μN μG ν : Measure (Mt k r)}
    {σ : Mx k r → (H →L[ℂ] H)} (hG : GHyp z π μW μN μG ν σ) :
    SFinite μW ∧ SFinite μN ∧ SFinite ν ∧ μG = (ν.prod (μW.prod μN)).map psiMap := by
  obtain ⟨-, hGh, -, -, ⟨hWh, -⟩, ⟨κ, -, -, hκ⟩, hq⟩ := hG
  have : SigmaFinite μG := hGh.1
  have : SigmaFinite μW := hWh.1
  have : SFinite μN := by rw [hκ]; infer_instance
  have : SFinite (muSof μW μN) := by unfold muSof; infer_instance
  have : SFinite ν := sfinite_quot hGh.2.1 hq
  exact ⟨inferInstance, inferInstance, inferInstance, quot_map hq⟩

theorem weilStep : WeilStep := by
  intro k r H _ _ _ Wp _ _ _ _ z π μW μN μG ν σ hG F hF
  obtain ⟨hWs, hNs, hνs, hmap⟩ := gHyp_sfinite hG
  subst hmap
  have hFm := hF.aestronglyMeasurable
  have hI := (integrable_map_measure hFm measurable_psiMap.aemeasurable).1 hF
  refine ⟨hI.prod_right_ae, hI.integral_prod_left, ?_⟩
  rw [integral_map measurable_psiMap.aemeasurable hFm, integral_prod (fun w => F (Matrix.of (psiMap w))) hI]
  rfl

theorem nuStep : NuStep := by
  intro k r H _ _ _ Wp _ _ _ _ z π μW μN μG ν σ hG
  obtain ⟨hWs, hNs, hνs, hmap⟩ := gHyp_sfinite hG
  obtain ⟨-, hGh, -, -, ⟨hWh, -⟩, ⟨κ, -, -, hκ⟩, hq⟩ := hG
  have hS0 : μW.prod μN ≠ 0 := fun h0 =>
    muS_ne_zero hGh.2.1 hq (by rw [muSof, h0, Measure.map_zero])
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := ae_iff.2 hGh.2.2.1
  rw [hmap] at hGae
  have h1 := Measure.ae_ae_of_ae_prod (ae_of_ae_map measurable_psiMap.aemeasurable hGae)
  have hWae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UH (Hpk k r) ∧ Matrix.of p.2 ∈ UH (Hpk k r) := by
    have a1 : ∀ᵐ y ∂μW, Matrix.of y ∈ UWset k r z := ae_iff.2 hWh.2.2.1
    have a2 : ∀ᵐ y ∂μN, Matrix.of y ∈ Nset k r := by
      rw [hκ]
      exact ae_iff.2 (PI.WUN.muN_conc κ)
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae a1,
      Measure.quasiMeasurePreserving_snd.ae a2] with p hp1 hp2
    exact ⟨hp1.1, hp2.1⟩
  have : (ae (μW.prod μN)).NeBot := ae_neBot.2 hS0
  filter_upwards [h1] with x hx
  obtain ⟨p, hp, hp'⟩ := (hx.and hWae).exists
  have hpx : sM p * Matrix.of x ∈ UH (Hpk k r) := hp
  have hs : sM p ∈ UH (Hpk k r) := PI.WUN.UH_mul hp'.1 hp'.2
  have h2 := PI.WUN.UH_mul (PI.WUN.UH_inv hs) hpx
  rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (PI.WUN.UH_det hs), Matrix.one_mul] at h2

end Weil

end PI.WBL.FSW
