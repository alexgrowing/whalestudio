import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionStableBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_completion_stable_base_change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (m : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), (∀ z ∈ GlobalTheory.ThK.latHat X, m.mulVec z ∈ GlobalTheory.ThK.latHat X) → ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)), (m.map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E))).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.FinPartLat.finite_part | exact GlobalTheory.FinPartLat.finite_part | (intros; apply GlobalTheory.FinPartLat.finite_part <;> assumption)
