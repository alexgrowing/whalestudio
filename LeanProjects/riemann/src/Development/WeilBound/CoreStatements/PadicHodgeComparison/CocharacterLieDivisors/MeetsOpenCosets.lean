import Mathlib

open Polynomial

namespace PositivityTheory.AutomorphicGaloisHodgeTate.Div

def MeetsOpenCosets {Γ : Type} [Group Γ] [TopologicalSpace Γ] (S : Set Γ) : Prop :=
  ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → ∀ g : Γ, ∃ s ∈ S, g⁻¹ * s ∈ U

def IsSSMat {Γ K ι : Type} [Group Γ] [Field K] [Fintype ι] [DecidableEq ι]
    (ρ : Γ →* GL ι K) : Prop :=
  ∀ W : Submodule K (ι → K), (∀ g : Γ, ∀ v ∈ W, (ρ g : Matrix ι ι K).mulVec v ∈ W) →
    ∃ W' : Submodule K (ι → K), IsCompl W W' ∧
      ∀ g : Γ, ∀ v ∈ W', (ρ g : Matrix ι ι K).mulVec v ∈ W'

def InLieZar {Γ K K' ι : Type} [Group Γ] [Field K] [Field K'] [Algebra K K']
    [Fintype ι] [DecidableEq ι] (ρ : Γ →* GL ι K) (X : Matrix ι ι K') : Prop :=
  ∀ f : MvPolynomial (ι × ι) K,
    (∀ g : Γ, MvPolynomial.eval (fun p : ι × ι => (ρ g : Matrix ι ι K) p.1 p.2) f = 0) →
      ∑ p : ι × ι, algebraMap K K'
          (MvPolynomial.eval (fun q : ι × ι => (1 : Matrix ι ι K) q.1 q.2)
            (MvPolynomial.pderiv p f)) * X p.1 p.2 = 0

def DivCore : Prop :=
  ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K K' : Type) [Field K] [IsAlgClosed K] [CharZero K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [Field K'] [IsAlgClosed K'] [Algebra K K']
    (n m : ℕ), 0 < m →
    ∀ ρ : Γ →* GL (Fin n × Fin m) K,
      Continuous (fun g : Γ => (ρ g : Matrix (Fin n × Fin m) (Fin n × Fin m) K)) →
      IsSSMat ρ →
    ∀ (S : Set Γ), Dense S →
    ∀ (P : Γ → K[X]), (∀ s ∈ S, (P s).Monic) →
      (∀ s ∈ S, (ρ s : Matrix (Fin n × Fin m) (Fin n × Fin m) K).charpoly = (P s) ^ m) →
    ∀ (X : Matrix (Fin n × Fin m) (Fin n × Fin m) K') (Q : K'[X]),
      InLieZar ρ X → X.charpoly = Q ^ m → Q.Separable →
    ∃ r : Γ →* GL (Fin n) K,
      Continuous (fun g : Γ => (r g : Matrix (Fin n) (Fin n) K)) ∧ IsSSMat r ∧
      (∀ s ∈ S, (r s : Matrix (Fin n) (Fin n) K).charpoly = P s) ∧
      ∃ A : GL (Fin n × Fin m) K, ∀ g : Γ,
        (A : Matrix (Fin n × Fin m) (Fin n × Fin m) K) *
            (ρ g : Matrix (Fin n × Fin m) (Fin n × Fin m) K) *
            ((A⁻¹ : GL (Fin n × Fin m) K) : Matrix (Fin n × Fin m) (Fin n × Fin m) K) =
          Matrix.kronecker (r g : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin m) (Fin m) K)

def MultGeneric {K : Type} [Field K] (Q : K[X]) : Prop :=
  Q.Separable ∧ ∀ x ∈ Q.roots, ∀ y ∈ Q.roots, x ≠ y → ∀ k : ℕ, 0 < k → (x / y) ^ k ≠ 1

def DivGenOne : Prop :=
  ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K]
    (n m : ℕ), 0 < m →
    ∀ ρ : Γ →* GL (Fin n × Fin m) K,
      Continuous (fun g : Γ => (ρ g : Matrix (Fin n × Fin m) (Fin n × Fin m) K)) →
      IsSSMat ρ →
    ∀ (S : Set Γ), Dense S →
    ∀ (P : Γ → K[X]), (∀ s ∈ S, (P s).Monic) →
      (∀ s ∈ S, (ρ s : Matrix (Fin n × Fin m) (Fin n × Fin m) K).charpoly = (P s) ^ m) →
      (∃ s₀ ∈ S, MultGeneric (P s₀)) →
    ∃ r : Γ →* GL (Fin n) K,
      Continuous (fun g : Γ => (r g : Matrix (Fin n) (Fin n) K)) ∧ IsSSMat r ∧
      (∀ s ∈ S, (r s : Matrix (Fin n) (Fin n) K).charpoly = P s) ∧
      ∃ A : GL (Fin n × Fin m) K, ∀ g : Γ,
        (A : Matrix (Fin n × Fin m) (Fin n × Fin m) K) *
            (ρ g : Matrix (Fin n × Fin m) (Fin n × Fin m) K) *
            ((A⁻¹ : GL (Fin n × Fin m) K) : Matrix (Fin n × Fin m) (Fin n × Fin m) K) =
          Matrix.kronecker (r g : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin m) (Fin m) K)

end PositivityTheory.AutomorphicGaloisHodgeTate.Div
