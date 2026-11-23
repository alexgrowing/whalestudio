import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainCoboundaryOfClassZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialCochain_coboundary_of_class_zero : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (s : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F), IsCls s (0 : H R E F ((1 : ℕ) : ℤ)) → ∃ t : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, s = cobd t := by
  first | (exact @GlobalTheory.CechOne.cobd_of_isCls_zero) | (exact GlobalTheory.CechOne.cobd_of_isCls_zero) | (intros; apply GlobalTheory.CechOne.cobd_of_isCls_zero  <;> assumption)
