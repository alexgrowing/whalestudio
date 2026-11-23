import Mathlib
import Formalism.LogFactorialIndices.StatementIdx

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

def IsLatticeSpanImage : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ M : Submodule O V, Formalism.LatticeIndexTer.IsLat O K V M →
      Formalism.LatticeIndexTer.IsLat O' K' V₁ (Submodule.span O' (j '' (M : Set V)))

def FinrankSpanImage : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ V' : Submodule K V, finrank K' (Submodule.span K' (j '' (V' : Set V))) = finrank K V'

def SpanImageInf : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ (M : Submodule O V) (V' : Submodule K V), Formalism.LatticeIndexTer.IsLat O K V M →
      Submodule.span O' (j '' (M : Set V)) ⊓
          (Submodule.span K' (j '' (V' : Set V))).restrictScalars O' =
        Submodule.span O' (j '' ((M ⊓ V'.restrictScalars O : Submodule O V) : Set V))

def RelIndexSpanImage : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ A B : Submodule O V, A.FG → B.FG →
      Submodule.span K (A : Set V) = Submodule.span K (B : Set V) →
      Formalism.LatticeIndexTer.idx O' V₁ (Submodule.span O' (j '' (A : Set V)))
                (Submodule.span O' (j '' (B : Set V))) =
        Formalism.LatticeIndexTer.idx O V A B

def LocalStepDescent : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ (M Θ : Submodule O V) (V' : Submodule K V), Formalism.LatticeIndexTer.IsLat O K V M →
      Formalism.LatticeIndexTer.IsLat O K V Θ → ∀ (d Y Z : ℝ) (e : ℕ),
      d * (Formalism.LatticeIndexTer.idx O' V₁
            (Submodule.span O' (j '' (M : Set V)) ⊓
              (Submodule.span K' (j '' (V' : Set V))).restrictScalars O')
            (Submodule.span O' (j '' (Θ : Set V)) ⊓
              (Submodule.span K' (j '' (V' : Set V))).restrictScalars O') : ℝ) ≤
          d * ((e : ℝ) * (finrank K' (Submodule.span K' (j '' (V' : Set V))) : ℝ) + Y) + Z →
        d * (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
          d * ((e : ℝ) * (finrank K V' : ℝ) + Y) + Z

def AddValAlgebraMap : Prop :=
  ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'],
    ∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ a : O, a ≠ 0 →
      IsDiscreteValuationRing.addVal O' (algebraMap O O' a) = IsDiscreteValuationRing.addVal O a

def FinrankNormTensor : Prop :=
  ∀ (K K' K₁ : Type) [Field K] [Field K'] [Algebra K K'] [Field K₁] [Algebra K K₁]
    [FiniteDimensional K K₁],
    finrank K' (TensorProduct K K' K₁) = finrank K K₁ ∧
      ∀ x : K₁, Algebra.norm K' (TensorProduct.tmul K (1 : K') x) =
        algebraMap K K' (Algebra.norm K x)

end Formalism.LatticeBaseChangeAlt
