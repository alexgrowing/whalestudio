import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoalternatingExactOfFiniteTypeIsoFilteredColimit
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coalternatingExact_of_finiteType_iso_filteredColimits : ∀ (N M : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact M (coAug g)) → ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact N (coAug g) := by
  first | (exact @GlobalTheory.EtC.wExact_of_finiteType_iso) | (exact GlobalTheory.EtC.wExact_of_finiteType_iso) | (intros; apply GlobalTheory.EtC.wExact_of_finiteType_iso  <;> assumption)
