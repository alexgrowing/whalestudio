import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReduced
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced : ∀ (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [LocallyCompactSpace B] [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B], IsArtinianRing B → IsReduced B → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [MeasurableSpace (κ → B)] [BorelSpace (κ → B)] (M : Matrix κ κ B) (hM : IsUnit M.det), addEquivAddHaarChar (mulVecCE M hM) = modu B M.det := by
  first | exact @GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE | exact GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE | (intros; apply GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE <;> assumption)
