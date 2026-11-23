import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleOfMapToDegreeOneTerm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_of_map_to_degreeOne_term : ∀ (C : Shv ℤ) (I : Cx ℤ) (ψ : C ⟶ I.X 1), ψ ≫ I.d 1 2 = 0 → ∃ w : Cocycle (sgl C) I 1, sglι C ≫ w.1.v 0 1 (zero_add 1) = ψ := by
  first | (exact @GlobalTheory.EtC.exists_cocycle_of_map_to_X_one) | (exact GlobalTheory.EtC.exists_cocycle_of_map_to_X_one) | (intros; apply GlobalTheory.EtC.exists_cocycle_of_map_to_X_one  <;> assumption)
