import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceAt

set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem frMapO_add (x y : WO S T) : frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add (toEAf D) (fun a b => (toEAf D).map_add a b), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_zero : frMapO S T βS βT 0 = 0 := by
  unfold frMapO
  rw [Matrix.map_zero (toEAf D) (toEAf D).map_zero, Matrix.mul_zero, Matrix.zero_mul]

theorem frMapO_nsmul (k : ℕ) (x : WO S T) : frMapO S T βS βT (k • x) = k • frMapO S T βS βT x := by
  induction k with
  | zero => rw [zero_smul, zero_smul, frMapO_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, frMapO_add, ih]

end Formalism.IndefR.Fin

end
