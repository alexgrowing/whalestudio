import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

def IdeleTop : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    (IsTopologicalRing (AE F E) ∧ LocallyCompactSpace (AE F E) ∧ SecondCountableTopology (AE F E) ∧ T2Space (AE F E)) ∧
    LocallyCompactSpace (AE F E)ˣ ∧ SecondCountableTopology (AE F E)ˣ ∧ T2Space (AE F E)ˣ ∧ IsTopologicalGroup (AE F E)ˣ ∧
    BorelSpace (AE F E)ˣ ∧
    ∀ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure → SigmaFinite μ ∧ μ.IsInvInvariant ∧ μ.IsMulRightInvariant ∧ μ.Regular

theorem ideleTop : IdeleTop := by
  intro F E _ _ _ _ _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI h1 : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI h2 : LocallyCompactSpace (AE F E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI h3 : SecondCountableTopology (AE F E) := e0.secondCountableTopology
  haveI h4 : T2Space (AE F E) := e0.isEmbedding.t2Space
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI h5 : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI h6 : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI h7 : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  exact ⟨⟨h1, h2, h3, h4⟩, h6, h5, inferInstance, inferInstance, h7, fun μ _ =>
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩⟩

end PositivityTheory.ThKCT

end
