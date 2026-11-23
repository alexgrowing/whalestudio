import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TeichmullerExtensionOfScalars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
open GlobalTheory.RingChain
open scoped TensorProduct Pointwise ChangeOfRings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_extension_of_scalars : ∀ (p k : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (g : R) (u : Rˣ) (s : R →+* R ⧸ Ideal.span {g}), (p : R) ∣ g ^ p ^ k → (∀ r : R, ∃ x : R, s r = Ideal.Quotient.mk _ x ∧ x ^ p ^ k - r ∈ Ideal.span {(p : R)}) → ∀ (P M : Type) [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M] (lam : P →+ M) (e : (ModuleCat.extendScalars s).obj (ModuleCat.of R P) ≃+ M), (∀ (r : R) (y : P), e ((Ideal.Quotient.mk _ r : R ⧸ Ideal.span {g}) ⊗ₜ[R, s] y) = r • lam y) → ∃ κ : M →+ P ⧸ (p : R) • (⊤ : Submodule R P), (∀ y, κ (lam y) = Submodule.Quotient.mk ((u : R) • y)) ∧ IsFrobLin R p (p ^ k) κ := by
  first | exact @GlobalTheory.RingChain.exists_isFrobLin_twist | exact GlobalTheory.RingChain.exists_isFrobLin_twist | (intros; apply GlobalTheory.RingChain.exists_isFrobLin_twist <;> assumption)
