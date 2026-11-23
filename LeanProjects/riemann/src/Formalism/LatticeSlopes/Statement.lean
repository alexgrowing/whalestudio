import Mathlib

open Module Submodule

noncomputable section

namespace Formalism.F

section Defs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in

def covol (L : Submodule ℤ E) : ℝ :=
  if h : DiscreteTopology L then
    haveI := h
    Real.sqrt (Matrix.gram ℝ (fun i => ((Module.finBasis ℤ L i : L) : E))).det
  else 0

def rk (L : Submodule ℤ E) : ℕ := Module.finrank ℤ L

def deg (L : Submodule ℤ E) : ℝ := -Real.log (covol L)

def slope (L : Submodule ℤ E) : ℝ := deg L / (rk L : ℝ)

def slopes (L : Submodule ℤ E) : Set ℝ :=
  {t | ∃ N : Submodule ℤ E, N ≤ L ∧ N ≠ ⊥ ∧ slope N = t}

def muMax (L : Submodule ℤ E) : ℝ := sSup (slopes L)

def IsSaturated (L N : Submodule ℤ E) : Prop :=
  N ≤ L ∧ ∀ x ∈ L, x ∈ Submodule.span ℝ (N : Set E) → x ∈ N

def quot (L N : Submodule ℤ E) : Submodule ℤ E :=
  L.map (((Submodule.span ℝ (N : Set E))ᗮ.starProjection : E →L[ℝ] E).toLinearMap.restrictScalars ℤ)

end Defs

def CovolEqGram : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ L), covol L = Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det

def CovolPos : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E), DiscreteTopology L → 0 < covol L

def CovolBasic : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    covol (⊥ : Submodule ℤ E) = 1 ∧
    ∀ v : E, v ≠ 0 → covol (Submodule.span ℤ ({v} : Set E)) = ‖v‖

def CovolEqCovolume : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L],
    covol L = ZLattice.covolume L

def GramDetLe : Prop :=
  ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (v : ι → E) (w : ι → F) (C : ℝ),
    (∀ c : ι → ℝ, ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖) →
    (Matrix.gram ℝ w).det ≤ C ^ (2 * Fintype.card ι) * (Matrix.gram ℝ v).det

def SlopeLeMuMax : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L N : Submodule ℤ E), DiscreteTopology L → N ≤ L → N ≠ ⊥ → slope N ≤ muMax L

def MuMaxAttained : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E), DiscreteTopology L → L ≠ ⊥ →
    ∃ N : Submodule ℤ E, IsSaturated L N ∧ N ≠ ⊥ ∧ slope N = muMax L

def SlopeInequality : Prop :=
  ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Submodule ℤ E) (M : Submodule ℤ F), DiscreteTopology L → DiscreteTopology M → L ≠ ⊥ →
    ∀ (φ : L →ₗ[ℤ] M) (C : ℝ), Function.Injective φ →
    (∀ x : L, ‖((φ x : M) : F)‖ ≤ C * ‖(x : E)‖) →
    slope L ≤ muMax M + Real.log C

def DegQuot : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L N : Submodule ℤ E), DiscreteTopology L → IsSaturated L N →
    DiscreteTopology (quot L N) ∧ rk L = rk N + rk (quot L N) ∧ deg L = deg N + deg (quot L N)

def MuMaxMono : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L N : Submodule ℤ E), DiscreteTopology L → N ≤ L → N ≠ ⊥ → muMax N ≤ muMax L

def OrthSum : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L₁ L₂ : Submodule ℤ E), DiscreteTopology L₁ → DiscreteTopology L₂ →
    (∀ x ∈ L₁, ∀ y ∈ L₂, inner ℝ x y = 0) →
    DiscreteTopology (L₁ ⊔ L₂ : Submodule ℤ E) ∧ deg (L₁ ⊔ L₂) = deg L₁ + deg L₂ ∧
    (L₁ ≠ ⊥ → L₂ ≠ ⊥ → muMax (L₁ ⊔ L₂) = max (muMax L₁) (muMax L₂))

def MuMaxLeMin : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E), DiscreteTopology L → L ≠ ⊥ → ∀ r : ℝ, 0 < r →
    (∀ x ∈ L, x ≠ 0 → r ≤ ‖x‖) → muMax L ≤ -Real.log r + Real.log (rk L : ℝ) / 2

end Formalism.F
