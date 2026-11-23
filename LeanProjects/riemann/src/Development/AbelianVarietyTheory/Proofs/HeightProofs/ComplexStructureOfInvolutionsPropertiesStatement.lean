import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ComplexStructureOfInvolutionsProperties
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexStructureOfInvolutions_properties : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') → (∀ x, jAt V W τ s s' (jAt V W τ s s' x) = -x) ∧ (∀ x y, symplC V W τ (jAt V W τ s s' x) (jAt V W τ s s' y) = symplC V W τ x y) ∧ (∀ g h, Commute g (thAt V τ s) → Commute h (thAt W τ s') → ∀ x, jAt V W τ s s' (actC V W g h x) = actC V W g h (jAt V W τ s s' x)) ∧ ∃ g ∈ KAt V τ s, ∃ h ∈ KAt W τ s', ∀ x, jAt V W τ s s' x = actC V W g h x := by
  first | exact @GlobalTheory.FockCxAlg.cx_alg | exact GlobalTheory.FockCxAlg.cx_alg | (intros; apply GlobalTheory.FockCxAlg.cx_alg <;> assumption)
