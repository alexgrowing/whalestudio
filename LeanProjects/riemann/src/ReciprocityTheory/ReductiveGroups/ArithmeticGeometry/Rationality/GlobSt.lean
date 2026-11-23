import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotSt

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField

noncomputable def logN {K₁ : Type*} [Field K₁] [NumberField K₁]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ)

def GlobalQuotStatement : Prop :=
  ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (ρ : ℕ) (m : Matrix (Fin ρ) (Fin ρ) K₁),
    m.det ≠ 0 →
    ∀ (s : Fin ρ → IsDedekindDomain.HeightOneSpectrum (𝓞 K₁) → ℝ)
      (β : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁) → ℝ)
      (a b : Fin ρ → InfinitePlace K₁ → ℝ) (B : Fin ρ → ℝ) (Bfin : ℝ),
      (∀ i, (Function.support (s i)).Finite) → (Function.support β).Finite →
      (∀ (σ : InfinitePlace K₁) (i j : Fin ρ), m i j ≠ 0 →
        Real.log (σ (m i j)) + a i σ ≤ b j σ) →
      (∀ i, ((∑ᶠ w, s i w * logN w) - ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * a i σ) /
          (Module.finrank ℚ K₁ : ℝ) ≤ B i) →
      (∑ᶠ w, β w * logN w) / (Module.finrank ℚ K₁ : ℝ) ≤ Bfin →
      (∑ᶠ w, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w) /
          (Module.finrank ℚ K₁ : ℝ) ≤
        ∑ j, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) / (Module.finrank ℚ K₁ : ℝ) +
          (ρ : ℝ) / 2 * Real.log ρ + ∑ i, B i + ρ * Bfin

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
