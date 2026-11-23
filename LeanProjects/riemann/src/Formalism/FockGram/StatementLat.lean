import Mathlib

open Matrix LinearMap Module

noncomputable section

namespace Formalism.E

def sgram {R M ι : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid M] [Module R M]
    (B : M →ₗ⋆[R] M →ₗ[R] R) (v : ι → M) : Matrix ι ι R :=
  Matrix.of fun i j => B (v i) (v j)

def bgram {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (B : LinearMap.BilinForm R M) (v : ι → M) : Matrix ι ι R :=
  Matrix.of fun i j => B (v i) (v j)

def orthSum {R M₁ M₂ : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R) :
    (M₁ × M₂) →ₗ⋆[R] (M₁ × M₂) →ₗ[R] R :=
  (B₁.comp (LinearMap.fst R M₁ M₂)).compl₂ (LinearMap.fst R M₁ M₂) +
    (B₂.comp (LinearMap.snd R M₁ M₂)).compl₂ (LinearMap.snd R M₁ M₂)

def GramChange : Prop :=
  ∀ (R M ι κ : Type) [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι] (B : M →ₗ⋆[R] M →ₗ[R] R) (b : Basis ι R M) (v : κ → M),
    sgram B v = (b.toMatrix v)ᴴ * sgram B b * b.toMatrix v

def GramChangeDet : Prop :=
  ∀ (R M ι : Type) [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι] (B : M →ₗ⋆[R] M →ₗ[R] R) (b : Basis ι R M) (v : ι → M),
    (sgram B v).det = star (b.det v) * b.det v * (sgram B b).det

def SubIndexNorm : Prop :=
  ∀ (S M ι : Type) [CommRing S] [AddCommGroup M] [Module S M]
    [Module.Free ℤ S] [Module.Finite ℤ S] [Fintype ι] [DecidableEq ι]
    (b : Basis ι S M) (N : Submodule S M) (bN : Basis ι S N),
    Nat.card (M ⧸ N) = (Algebra.norm ℤ (b.det fun i => (bN i : M))).natAbs

def SubIndexZ : Prop :=
  ∀ (M ι : Type) [AddCommGroup M] [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℤ M) (b : Basis ι ℤ M) (N : Submodule ℤ M) (bN : Basis ι ℤ N),
    (bgram B fun i => (bN i : M)).det = (Nat.card (M ⧸ N) : ℤ) ^ 2 * (bgram B b).det

def OrthSumGram : Prop :=
  ∀ (R M₁ M₂ ι₁ ι₂ : Type) [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R) (v₁ : ι₁ → M₁) (v₂ : ι₂ → M₂),
    sgram (orthSum B₁ B₂) (Sum.elim (fun i => (v₁ i, 0)) (fun j => (0, v₂ j))) =
      Matrix.fromBlocks (sgram B₁ v₁) 0 0 (sgram B₂ v₂) ∧
    (sgram (orthSum B₁ B₂) (Sum.elim (fun i => (v₁ i, 0)) (fun j => (0, v₂ j)))).det =
      (sgram B₁ v₁).det * (sgram B₂ v₂).det

def TensorGram : Prop :=
  ∀ (R M₁ M₂ ι₁ ι₂ : Type) [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B₁ : LinearMap.BilinForm R M₁) (B₂ : LinearMap.BilinForm R M₂) (v₁ : ι₁ → M₁)
    (v₂ : ι₂ → M₂),
    bgram (B₁.tmul B₂) (fun p : ι₁ × ι₂ => v₁ p.1 ⊗ₜ[R] v₂ p.2) =
      Matrix.kroneckerMap (· * ·) (bgram B₁ v₁) (bgram B₂ v₂) ∧
    (bgram (B₁.tmul B₂) (fun p : ι₁ × ι₂ => v₁ p.1 ⊗ₜ[R] v₂ p.2)).det =
      (bgram B₁ v₁).det ^ Fintype.card ι₂ * (bgram B₂ v₂).det ^ Fintype.card ι₁

def DualIndexZ : Prop :=
  ∀ (V ι : Type) [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℚ V) (b : Basis ι ℚ V), B.Nondegenerate →
    (Submodule.span ℤ (Set.range b) ≤ B.dualSubmodule (Submodule.span ℤ (Set.range b)) ↔
      ∀ i j, ∃ n : ℤ, B (b i) (b j) = n) ∧
    (Submodule.span ℤ (Set.range b) ≤ B.dualSubmodule (Submodule.span ℤ (Set.range b)) →
      ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex
          (B.dualSubmodule (Submodule.span ℤ (Set.range b))).toAddSubgroup : ℚ) =
        |(bgram B b).det| ∧
      (B.dualSubmodule (Submodule.span ℤ (Set.range b)) = Submodule.span ℤ (Set.range b) ↔
        |(bgram B b).det| = 1))

def CovolGram : Prop :=
  ∀ (E ι : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E),
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) = Real.sqrt (Matrix.gram ℝ b).det

end Formalism.E
