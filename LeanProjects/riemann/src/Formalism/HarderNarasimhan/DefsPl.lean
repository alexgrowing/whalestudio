import Formalism.HarderNarasimhan.StatementPl
import Formalism.HarderNarasimhan.DegSupermodZ

open Module NumberField

noncomputable section

namespace Formalism.HN

def placePart {P ι : Type*} [Fintype P] [Fintype ι] (v : P) :
    Submodule ℝ (EuclideanSpace ℝ (P × ι × Fin 2)) :=
  ⨅ (p : P × ι × Fin 2) (_ : p.1 ≠ v), LinearMap.ker (EuclideanSpace.proj p : EuclideanSpace ℝ (P × ι × Fin 2) →L[ℝ] ℝ).toLinearMap

def PlaceSplit : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ N : Submodule (𝓞 K) V, N.FG →
      Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
        (⨆ v, Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set _) ⊓ placePart v) ∧
      ∀ v, Module.finrank ℝ
        (Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓
          placePart v : Submodule ℝ _) = 2 * rkK N

def GramBlock : Prop :=
  ∀ (P E E' ι : Type) [Fintype P] [DecidableEq P] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    (Ev : P → Submodule ℝ E) (Ev' : P → Submodule ℝ E') (T : E →ₗ[ℝ] E') (c : P → ℝ)
    (W : Submodule ℝ E) (u : ι → E),
    (∀ v w, v ≠ w → ∀ x ∈ Ev v, ∀ y ∈ Ev w, inner ℝ x y = 0) →
    (∀ v w, v ≠ w → ∀ x ∈ Ev' v, ∀ y ∈ Ev' w, inner ℝ x y = 0) →
    (∀ v, 0 ≤ c v) → (∀ v, ∀ x ∈ Ev v, T x ∈ Ev' v ∧ ‖T x‖ ≤ c v * ‖x‖) →
    W = (⨆ v, W ⊓ Ev v) → LinearIndependent ℝ u → Submodule.span ℝ (Set.range u) = W →
    (Matrix.gram ℝ (fun i => T (u i))).det ≤
        (∏ v, c v ^ (2 * Module.finrank ℝ (W ⊓ Ev v : Submodule ℝ E))) * (Matrix.gram ℝ u).det ∧
      ((∀ v, ∀ x ∈ Ev v, ∀ y ∈ Ev v, inner ℝ (T x) (T y) = c v ^ 2 * inner ℝ x y) →
        (Matrix.gram ℝ (fun i => T (u i))).det =
          (∏ v, c v ^ (2 * Module.finrank ℝ (W ⊓ Ev v : Submodule ℝ E))) * (Matrix.gram ℝ u).det)

end Formalism.HN
