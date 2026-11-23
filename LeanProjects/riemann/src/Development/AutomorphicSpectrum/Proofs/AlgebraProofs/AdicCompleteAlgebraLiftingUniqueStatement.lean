import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AdicCompleteAlgebraLiftingUnique
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adic_complete_algebra_lifting_unique : ∀ (R A B : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Module.Finite R A] (I : Ideal R) [IsAdicComplete I R] (f : ∀ e : ℕ, B →ₐ[R] A ⧸ (I ^ (e + 1)).map (algebraMap R A)), (∀ e (b : B) (a : A), Ideal.Quotient.mk _ a = f (e + 1) b → Ideal.Quotient.mk _ a = f e b) → ∃! g : B →ₐ[R] A, ∀ e b, Ideal.Quotient.mk _ (g b) = f e b := by
  first | exact @GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique | exact GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique | (intros; apply GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique <;> assumption)
