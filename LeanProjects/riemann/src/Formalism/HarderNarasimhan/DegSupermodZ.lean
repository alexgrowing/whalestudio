import Formalism.HarderNarasimhan.Statement
import Formalism.LatticeSlopes.CovolAntiSameRank

open Module Submodule

noncomputable section

namespace Formalism.HN

def DegSupermodZ : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L A B : Submodule ℤ E), DiscreteTopology L → A ≤ L → B ≤ L →
    Formalism.F.rk (A ⊔ B) + Formalism.F.rk (A ⊓ B) = Formalism.F.rk A + Formalism.F.rk B ∧
    Formalism.F.deg A + Formalism.F.deg B ≤ Formalism.F.deg (A ⊔ B) + Formalism.F.deg (A ⊓ B)

def SatR : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L N : Submodule R V),
    IsLat ρ L → N ≤ L →
    ∃ N' : Submodule R V, N ≤ N' ∧ N' ≤ L ∧ zl ρ N' = Formalism.F.satur (zl ρ L) (zl ρ N)

def FinSup : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V)
    (S : Set (Submodule R V)), IsLat ρ L → (∀ N ∈ S, N ≤ L) →
    ∃ t : Finset (Submodule R V), (↑t : Set (Submodule R V)) ⊆ S ∧ sSup S = t.sup id

def SatBasic : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V),
    IsLat ρ L →
    (∀ N : Submodule R V, N ≤ L → IsLat ρ N) ∧
    (∀ A B : Submodule R V, A ≤ B → B ≤ L → rk ρ A ≤ rk ρ B ∧ (rk ρ A = rk ρ B → deg ρ A ≤ deg ρ B)) ∧
    (∀ S N : Submodule R V, IsSat ρ L S → S ≤ N → N ≤ L → rk ρ N = rk ρ S → N = S) ∧
    (∀ N : Submodule R V, N ≤ L → (rk ρ N = 0 ↔ N = ⊥)) ∧
    deg ρ (⊥ : Submodule R V) = 0 ∧ IsSat ρ L ⊥ ∧ IsSat ρ L L ∧
    (∀ S : Submodule R V, IsSat ρ L S →
      Formalism.F.rk (Formalism.F.quot (zl ρ L) (zl ρ S)) = rk ρ L - rk ρ S ∧
      rk ρ S ≤ rk ρ L ∧
      Formalism.F.deg (Formalism.F.quot (zl ρ L) (zl ρ S)) = deg ρ L - deg ρ S)

def RatioMax : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L S : Submodule R V),
    IsLat ρ L → IsSat ρ L S → S ≠ L →
    ∃ N : Submodule R V, S < N ∧ IsSat ρ L N ∧
      ∀ N' : Submodule R V, S < N' → N' ≤ L →
        (deg ρ N' - deg ρ S) * ((rk ρ N : ℝ) - rk ρ S) ≤
          (deg ρ N - deg ρ S) * ((rk ρ N' : ℝ) - rk ρ S)

end Formalism.HN
