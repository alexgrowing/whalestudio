import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardSubspacesKerTransposeEqCardRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_subspaces_ker_transpose_eq_card_range : ∀ (k : Type) [Field k] (m n j : ℕ) (z : Matrix (Fin m) (Fin n) k), Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W + j = m ∧ W ≤ LinearMap.ker zᵀ.mulVecLin} = Nat.card {W' : Submodule k (Fin m → k) // Module.finrank k W' = j ∧ LinearMap.range z.mulVecLin ≤ W'} := by
  first | exact @GlobalTheory.SplitHecke.card_le_ker_transpose_eq_card_range_le | exact GlobalTheory.SplitHecke.card_le_ker_transpose_eq_card_range_le | (intros; apply GlobalTheory.SplitHecke.card_le_ker_transpose_eq_card_range_le <;> assumption)
