import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FGTorsionFreeGen

namespace PI.FGTFG

def ProjStep : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M], Module.Projective R M

def SepStep : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] (m : M),
    m ≠ 0 → ∃ g : M →ₗ[R] R, g m ≠ 0

def CopStep : Prop :=
  ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (I J : Ideal R), I ≠ ⊥ → J ≠ ⊥ →
    ∃ a b : R, b ≠ 0 ∧ Ideal.span {a} * J ⊔ Ideal.span {b} * I = Ideal.span {b}

def SplitStep : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M], 2 ≤ Module.finrank R M →
    ∃ (φ : M →ₗ[R] R) (b : R), b ≠ 0 ∧ LinearMap.range φ = Ideal.span {b}

def RankOneStep : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M], Module.finrank R M = 1 →
    ∃ s : Finset M, s.card ≤ 2 ∧ Submodule.span R (s : Set M) = ⊤

end PI.FGTFG
