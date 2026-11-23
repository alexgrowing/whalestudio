import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSmoothAtOfSmoothQuotientPow

namespace GlobalTheory.SmoothAdic

open TensorProduct IsLocalRing

theorem isSmoothAt_of_smooth_quotient_pow : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (C : Type) [CommRing C] [Algebra R C] [Algebra.FiniteType R C], (∀ e : ℕ, Algebra.Smooth (R ⧸ I ^ (e + 1)) (TensorProduct R (R ⧸ I ^ (e + 1)) C)) → ∀ (q : Ideal C) [q.IsPrime], q.comap (algebraMap R C) = IsLocalRing.maximalIdeal R → Algebra.IsSmoothAt R q := by
  intro R _ _ _ I hI C _ _ _ h q _ hq
  refine GlobalTheory.SmoothLimit.isSmoothAt_of_smooth_quotient_pow (V := R) (A := C) (fun e => ?_) q hq
  have hle : I ^ (e + 1) ≤ maximalIdeal R ^ (e + 1) :=
    Ideal.pow_right_mono (le_maximalIdeal hI) (e + 1)
  let _ : Algebra (R ⧸ I ^ (e + 1)) (R ⧸ maximalIdeal R ^ (e + 1)) :=
    (Ideal.Quotient.factor hle).toAlgebra
  have : IsScalarTower R (R ⧸ I ^ (e + 1)) (R ⧸ maximalIdeal R ^ (e + 1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := h e
  exact Algebra.Smooth.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (R ⧸ I ^ (e + 1)) (R ⧸ maximalIdeal R ^ (e + 1))
      (R ⧸ maximalIdeal R ^ (e + 1)) C)

end GlobalTheory.SmoothAdic
