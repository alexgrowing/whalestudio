import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitFiniteTypeIntRings
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_filteredColimit_finiteType_int_rings : ∀ A : CommRingCat.{0}, ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (ι : D ⟶ (Functor.const J).obj A), Nonempty (IsColimit (Cocone.mk A ι)) ∧ ∀ j, Algebra.FiniteType ℤ (D.obj j) := by
  first | (exact @GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType) | (exact GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType) | (intros; apply GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType  <;> assumption)
