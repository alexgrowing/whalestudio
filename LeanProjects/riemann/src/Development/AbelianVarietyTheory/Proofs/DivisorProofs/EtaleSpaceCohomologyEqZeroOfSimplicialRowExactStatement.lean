import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (P : PSh) (g : disc.obj P ⟶ E), IsIso (g.app (op ⦋0⦌)) →
  ∀ (n : ℕ) (x : H R E F n), pull R g F n x = 0 →
  (∀ p : ℕ, p + 1 ≤ n → RowExact R E F ((n : ℤ) - ((p + 1 : ℕ) : ℤ)) p) → x = 0 := by
  first | (exact @GlobalTheory.EtC.vanish_of_rowExact) | (exact GlobalTheory.EtC.vanish_of_rowExact) | (intros; apply GlobalTheory.EtC.vanish_of_rowExact  <;> assumption)
