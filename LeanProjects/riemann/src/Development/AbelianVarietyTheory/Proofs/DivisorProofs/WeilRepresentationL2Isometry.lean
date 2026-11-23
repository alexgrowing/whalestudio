import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilL2Isometry

open MeasureTheory GlobalTheory.WeilAdm.HaarSplit
open scoped ENNReal Classical

theorem l2A_eq_of_isUnitaryOn : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {G : Type} [Group G]
    (om : G →* Module.End ℂ ((κ → AF F) → ℂ)), (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) → IsUnitaryOn (adeleClass F) om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A F μ Φ := by
  intro F _ _ κ _ G _ om hpres hU
  haveI := volume_isAddHaar F κ
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI hνH : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hμH : Measure.IsAddHaarMeasure (((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂(((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν) :=
    fun h => lintegral_map_equiv h em
  have key : ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilL2Words.l2A F ν Ψ = ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂(((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) := by
    intro Ψ hΨ
    rw [hint]
    have hHm : Measurable fun p => ‖Ψ (splitE F κ p)‖ₑ ^ 2 :=
      (continuous_comp_splitE F κ Ψ hΨ).measurable.enorm.pow_const 2
    rw [lintegral_prod_symm _ hHm.aemeasurable]
    rfl
  refine ⟨ν, hνH, fun p Φ hΦ => ?_⟩
  rw [key _ (hpres p Φ hΦ), key _ hΦ]
  exact hU _ hμH p Φ hΦ

end GlobalTheory.WeilL2Isometry
