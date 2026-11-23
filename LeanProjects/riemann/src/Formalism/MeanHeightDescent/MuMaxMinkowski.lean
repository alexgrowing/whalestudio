import Mathlib
import Formalism.HarderNarasimhan.StatementPl
import Formalism.QuotientMetricDivisors.Statement

open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

open Formalism.HN

def LcvMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ), 0 < d →
    ∀ X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ M : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K M →
      Formalism.DivisionValues.lcv X M = -((d : ℝ) * muDef (Pi.basisFun K (Fin d)) X M)

def DescentSlope : Prop :=
  ∀ (K V ι W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X' v).det) →
    ∀ (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W), A.FG → B.FG → A ≠ ⊥ →
      Function.Injective φ → A.map (φ.restrictScalars (𝓞 K)) ≤ B →
      (rkK A : ℝ) * (muDef b X A - htMap b X b' X' φ) +
          ((rkK B : ℝ) - (rkK A : ℝ)) * muMinDef b' X' B ≤
        (rkK B : ℝ) * muDef b' X' B

def SpanMuMin : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (B : Submodule (𝓞 K) V) (Λ : ℝ), B.FG → B ≠ ⊥ →
      (∃ s : Set V, s ⊆ (B : Set V) ∧ (∀ x ∈ s, ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ≤ Real.exp Λ) ∧
        (B : Set V) ⊆ (Submodule.span K s : Set V)) →
      -(2 * Λ) ≤ muMinDef b X B

def GoodBadCut : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (e : V →ₗ[K] V) (g : ℕ) (N : Submodule (𝓞 K) V), N.FG → 1 ≤ g →
      e ∘ₗ e = e →
      (∀ v x y, Formalism.HermitianLatticesTheory.majAt b X v (e x) y = Formalism.HermitianLatticesTheory.majAt b X v x (e y)) →
      (∀ x ∈ N, (g : K) • e x ∈ N) →
      rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) +
          rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) = rkK N ∧
      (rkK N : ℝ) * muDef b X N ≤
        (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) *
            muDef b X (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) +
          (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) *
            muDef b X (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) +
          2 * (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) * Real.log g ∧
      ∀ M : Submodule (𝓞 K) V, M.FG → N ≤ M →
        (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) *
            muDef b X (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) ≤
          (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) * muMaxDef b X M

def TwistLower : Prop :=
  ∀ (K V ι W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X' v).det) →
    ∀ (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W)
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), I ≠ 0 → A.FG → B.FG → A ≠ ⊥ →
      Function.Injective φ →
      Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) (A.map (φ.restrictScalars (𝓞 K))) ≤ B →
      rkK B = rkK A →
      muDef b X A - htMap b X b' X' φ -
          2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) ≤
        muDef b' X' B

def MuMaxMinkowski : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (B : Submodule (𝓞 K) V) (La : ℝ), B.FG → B ≠ ⊥ →
      (∀ x ∈ B, x ≠ 0 →
        -La ≤ (1 / (nPl K : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x)) →
      muMaxDef b X B ≤ 2 * La + Real.log (rkK B : ℝ) + logDisc K / (Module.finrank ℚ K : ℝ)

end Formalism.ExtensionFiltration
