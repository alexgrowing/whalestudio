import Mathlib
import Formalism.HarderNarasimhan.StatementPl

open Module NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SubquotientSizeInequality

open Formalism.HN Formalism.HermitianLatticesTheory

section Dist

variable {K : Type*} [Field K] [NumberField K] [StarRing K]
  {V ι : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

def ptAt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (y : V) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fcoord b X v y)

def spanAt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (S : Submodule (𝓞 K) V) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  Submodule.span ℂ (ptAt b X v '' (S : Set V))

def distAt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (S : Submodule (𝓞 K) V) (y : V) : ℝ :=
  Metric.infDist (ptAt b X v y) (spanAt b X v S : Set (EuclideanSpace ℂ ι))

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K] in
theorem norm_ptAt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (y : V) : ‖ptAt b X v y‖ = normAt b X v y := by
  simp [ptAt, normAt, cnorm, EuclideanSpace.norm_eq]

end Dist

def SizeIneqSubquot : Prop :=
  ∀ (K V ι W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X' v).det) →
    ∀ (φ : V →ₗ[K] W) (A A' : Submodule (𝓞 K) V) (B B' : Submodule (𝓞 K) W),
      A.FG → B.FG → IsSat (realize b X) A A' → IsSat (realize b' X') B B' →
      A.map (φ.restrictScalars (𝓞 K)) ≤ B → A'.map (φ.restrictScalars (𝓞 K)) ≤ B' →
      ¬ A.map (φ.restrictScalars (𝓞 K)) ≤ B' →
      ∀ lo hi : ℝ, 0 < lo →
        (∀ N : Submodule (𝓞 K) W, B' < N → N ≤ B → lo ≤ sizeQ b' X' N B') →
        (∀ N : Submodule (𝓞 K) V, A' ≤ N → IsSat (realize b X) A N → N ≠ A →
          sizeQ b X A N ≤ hi) →
        (∀ c : InfinitePlace K → ℝ, (∀ v, 0 ≤ c v) →
          (∀ v, ∀ y ∈ Submodule.span K (A : Set V),
            distAt b' X' v B' (φ y) ≤ c v * distAt b X v A' y) →
          lo / hi ≤ (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ))) ∧
        lo / hi ≤ (∏ v, opNormAt b X b' X' v φ) ^ ((1 : ℝ) / (nPl K : ℝ))

end GlobalTheory.IndefiniteRowSideFullHecke.SubquotientSizeInequality
