import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftSquareZeroOfFormallyEtaleAwayDepth
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algHom_lift_squareZero_of_formallyEtale_away_depth : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A], (∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g) (TensorProduct R (Localization.Away g) A)) → ∀ (S T : Type) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T], ReciprocityTheory.CA.ModDepthGE R S 2 → ReciprocityTheory.CA.ModDepthGE R T 1 → ∀ (π : S →ₐ[R] T), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (φ : A →ₐ[R] T), ∃ ψ : A →ₐ[R] S, π.comp ψ = φ := by
  first | exact @GlobalTheory.SquareZeroLift.squareZeroLift | exact GlobalTheory.SquareZeroLift.squareZeroLift | (intros; apply GlobalTheory.SquareZeroLift.squareZeroLift <;> assumption)
