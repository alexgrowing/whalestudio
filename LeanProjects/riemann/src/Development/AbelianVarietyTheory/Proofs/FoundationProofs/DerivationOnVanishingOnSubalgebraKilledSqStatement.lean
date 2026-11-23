import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnVanishingOnSubalgebraKilledSq
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationOn_vanishing_on_subalgebra_killed_sq : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S), IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → (∀ β ∈ B, D β = 0) → ∀ x ∈ C, (e * e) • D x = 0 := by
  first | exact @GlobalTheory.AlmostEt.derOn_killed_sq | exact GlobalTheory.AlmostEt.derOn_killed_sq | (intros; apply GlobalTheory.AlmostEt.derOn_killed_sq <;> assumption)
