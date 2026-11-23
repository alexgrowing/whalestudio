import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulMatrixRingHomTrace
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_mul_matrix_ring_hom_trace : ∀ (O : Type) [CommRing O] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ) (b : Module.Basis (Fin n) R Λ) (φ : R →+* O), (∃ ρ : Λ →+* Matrix (Fin n) (Fin n) O, ⇑ρ = fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) ∧ ∀ a : Λ, (((Algebra.leftMulMatrix b a).transpose).map φ).trace = φ (Algebra.trace R Λ a) := by
  first | exact @GlobalTheory.transposedRegularRep_ringHom_trace | exact GlobalTheory.transposedRegularRep_ringHom_trace | (intros; apply GlobalTheory.transposedRegularRep_ringHom_trace <;> assumption)
