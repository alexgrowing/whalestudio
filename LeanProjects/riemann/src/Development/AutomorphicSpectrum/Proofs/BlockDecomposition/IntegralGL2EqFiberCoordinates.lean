import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Row1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableFixedFunction
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GJTwo

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

open Classical in

def cellPsi (p : (Fin 2 → F) × F × F) : GL (Fin 2) F :=
  if h : p ∈ cellU F then cellG ⟨p, h⟩ else 1

def cellD (p : (Fin 2 → F) × F × F) : ℝ≥0 := ((modulus p.2.2 : ℝ) ^ (-2 : ℤ)).toNNReal

def cellNu (ψ : AddChar F Circle) : Measure ((Fin 2 → F) × F × F) :=
  ((cM ψ).restrict (cellU F)).withDensity fun p => (cellD p : ℝ≥0∞)

theorem measurable_cellPsi : Measurable (cellPsi : (Fin 2 → F) × F × F → GL (Fin 2) F) := by
  have hU : MeasurableSet (cellU F) := isOpen_cellU.measurableSet
  refine measurable_of_restrict_of_restrict_compl hU ?_ ?_
  · have he : (cellU F).domRestrict (cellPsi : _ → GL (Fin 2) F) = cellG := by
      funext p
      exact dif_pos p.2
    rw [he]
    exact continuous_cellG.measurable
  · have he : ((cellU F)ᶜ).domRestrict (cellPsi : _ → GL (Fin 2) F) = fun _ => 1 := by
      funext p
      exact dif_neg p.2
    rw [he]
    exact measurable_const

theorem measurable_cellD : Measurable (cellD : (Fin 2 → F) × F × F → ℝ≥0) := by
  have hm : Measurable fun p : (Fin 2 → F) × F × F => (modulus p.2.2 : ℝ) :=
    (NNReal.continuous_coe.comp (continuous_modulus.comp continuous_snd.snd)).measurable
  have he : (cellD : (Fin 2 → F) × F × F → ℝ≥0) =
      fun p => (((modulus p.2.2 : ℝ) ^ 2)⁻¹).toNNReal := by
    funext p
    simp only [cellD, _root_.zpow_neg]
    norm_cast
  rw [he]
  exact (hm.pow_const 2).inv.real_toNNReal

theorem lintegral_cell (hm : GJm1) {ψ : AddChar F Circle} (hψ : IsStd ψ)
    (f : GL (Fin 2) F → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂LFS.hG ψ =
      ∫⁻ p, (cellU F).indicator (fun p => f (cellPsi p) * (cellD p : ℝ≥0∞)) p ∂cM ψ := by
  have hU : MeasurableSet (cellU F) := isOpen_cellU.measurableSet
  have hG : Measurable ((cellU F).indicator (fun p => f (cellPsi p) * (cellD p : ℝ≥0∞))) :=
    ((hf.comp measurable_cellPsi).mul measurable_cellD.coe_nnreal_ennreal).indicator hU
  refine (hm F ψ hψ f hf).trans ?_
  rw [cM, lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun r => ?_
  have h2 : Measurable fun q : F × F =>
      (cellU F).indicator (fun p => f (cellPsi p) * (cellD p : ℝ≥0∞)) (r, q) :=
    hG.comp measurable_prodMk_left
  rw [lintegral_prod _ h2.aemeasurable]
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  by_cases h : y = 0 ∨ r 1 = 0
  · have hn : (r, x, y) ∉ cellU F := fun hc => h.elim hc.1 hc.2
    rw [dif_pos h]
    exact (Set.indicator_of_notMem hn _).symm
  · have hn : (r, x, y) ∈ cellU F := ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
    rw [dif_neg h]
    refine Eq.trans ?_ (Set.indicator_of_mem hn _).symm
    simp only [cellPsi, dif_pos hn]
    rfl

theorem hG_eq_map (hm : GJm1) {ψ : AddChar F Circle} (hψ : IsStd ψ) :
    LFS.hG ψ = Measure.map cellPsi (cellNu ψ) := by
  have hU : MeasurableSet (cellU F) := isOpen_cellU.measurableSet
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have h3 := lintegral_withDensity_eq_lintegral_mul ((cM ψ).restrict (cellU F))
    (measurable_cellD (F := F)).coe_nnreal_ennreal (hf.comp measurable_cellPsi)
  rw [lintegral_map hf measurable_cellPsi, lintegral_cell hm hψ f hf, cellNu,
    lintegral_indicator hU]
  refine Eq.trans ?_ h3.symm
  refine lintegral_congr fun p => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  exact mul_comm _ _

theorem Ff_eq (f : GL (Fin 2) F → ℂ) :
    Ff f = (cellU F).indicator fun p => (cellD p : ℝ) • (f ∘ cellPsi) p := by
  funext p
  by_cases h : p.2.2 = 0 ∨ p.1 1 = 0
  · have hn : p ∉ cellU F := fun hc => h.elim hc.1 hc.2
    rw [Set.indicator_of_notMem hn, Ff, dif_pos h]
  · have hn : p ∈ cellU F := ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
    rw [Set.indicator_of_mem hn, Ff, dif_neg h, Function.comp_apply, cellPsi, dif_pos hn,
      Complex.real_smul, mul_comm, cellD, Real.coe_toNNReal _ (by positivity)]
    rfl

end GlobalTheory.CompanionTheory.GJTwo
