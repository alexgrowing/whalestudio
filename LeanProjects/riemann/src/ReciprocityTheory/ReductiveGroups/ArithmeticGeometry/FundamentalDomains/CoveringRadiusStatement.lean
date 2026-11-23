import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Matrix ReciprocityTheory.MultiplicativeHeights

noncomputable def d5mu (f r : ℕ) (d laStar : ℝ) : ℝ := 4 * ((f : ℝ) * r) ^ 3 * d / laStar

def CoveringRadiusStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Type) [Fintype ι] [Nonempty ι]
    (r p : ℕ) (S : HermForm K r) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (laStar : ℝ),
    Function.Injective σ →
    (∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) →
    p ≤ r → 0 < laStar → (∀ i, (Q i).det ≠ 0) →
    (∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y)) →
    IsLattice L → IsSelfDual S L →
    (∀ v ∈ L, v ≠ 0 → ∃ i, laStar ^ 2 ≤ normSq (Q i *ᵥ embVec (σ i) v)) →
    let μ := d5mu (Fintype.card ι) r |(NumberField.discr K : ℝ)| laStar
    (∀ w : ι → Fin r → ℂ, ∃ l ∈ L, ∑ i, normSq (Q i *ᵥ embVec (σ i) l - w i) ≤ μ ^ 2) ∧
    ∃ v : Fin r → Fin r → K, (∀ j, v j ∈ L) ∧ LinearIndependent K v ∧ ∀ j, majSq σ Q (v j) ≤ μ ^ 2

end ReciprocityTheory.ChartRestriction.G.FD
