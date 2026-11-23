import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyPullback_eq_zero_of_cechOneCocycle : ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) (s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F), cobd s = 0 → ∀ x : H R (sch.obj X) F ((1 : ℕ) : ℤ), IsCls s (pull R (cechAug f) F ((1 : ℕ) : ℤ) x) → pull R (sch.map f) F ((1 : ℕ) : ℤ) x = 0 := by
  first | (exact @GlobalTheory.CechOne.pull_sch_eq_zero) | (exact GlobalTheory.CechOne.pull_sch_eq_zero) | (intros; apply GlobalTheory.CechOne.pull_sch_eq_zero  <;> assumption)
