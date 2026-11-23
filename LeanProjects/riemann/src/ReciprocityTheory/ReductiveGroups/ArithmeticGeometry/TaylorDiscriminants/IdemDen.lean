import Mathlib

noncomputable section

open NumberField TensorProduct

namespace ReciprocityTheory.ChartRestriction.G.TB

def trDual {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) :
    Module.Basis ι ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b

def idemOf {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [Algebra ℚ C] {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℚ E) (τ : E →+* C) : E ⊗[ℚ] C :=
  ∑ i, trDual b i ⊗ₜ[ℚ] τ (b i)

def evAt {E : Type} [Field E] {C : Type} [Field C] [Algebra ℚ E] [Algebra ℚ C] (σ : E →+* C) :
    E ⊗[ℚ] C →ₐ[ℚ] C :=
  Algebra.TensorProduct.productMap (σ.toRatAlgHom) (AlgHom.id ℚ C)

open Classical in

def IdemEvalSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] [IsAlgClosed C] (ι : Type) [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℚ E) (τ σ : E →+* C),
    evAt σ (idemOf b τ) = if σ = τ then 1 else 0

def DualDiffSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E),
    (∀ i, IsIntegral ℤ (b i)) →
    (∀ x : 𝓞 E, ∃ c : ι → ℤ, (x : E) = ∑ i, (c i : ℚ) • b i) →
    ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ i, IsIntegral ℤ ((δ : E) * trDual b i)

end ReciprocityTheory.ChartRestriction.G.TB
