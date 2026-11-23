import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDescendsAlongFlatExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
open TensorProduct GlobalTheory.PerfdLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_preimage_equiv_of_mod_regular_iso : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (f : A) (h : ℕ) (N : Submodule B (Fin h → B)) (L : Submodule A (Fin h → A)), IsSMulRegular B (algebraMap A B f) → (∀ x : B, ∃ (a : A) (y : B), x = algebraMap A B a + algebraMap A B f * y) → (∀ (a : A) (y : B), algebraMap A B a = algebraMap A B f * y → ∃ b, a = f * b) → (∀ y : Fin h → B, algebraMap A B f • y ∈ N) → (∀ x : Fin h → A, x ∈ L ↔ piMap (algebraMap A B) (Fin h) x ∈ N) → Nonempty (TensorProduct A B L ≃ₗ[B] N) := by
  first | exact @GlobalTheory.LatBaseChange.nonempty_tensor_equiv | exact GlobalTheory.LatBaseChange.nonempty_tensor_equiv | (intros; apply GlobalTheory.LatBaseChange.nonempty_tensor_equiv <;> assumption)
