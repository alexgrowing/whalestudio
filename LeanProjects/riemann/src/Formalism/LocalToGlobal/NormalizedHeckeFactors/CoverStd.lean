import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2

def HeckeStdPlain : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
    (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B →
    ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ),
      s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n →
      (∀ f ∈ NG.TypeSp a.ρ J χ, NG.tN J s ϖ k f ∈ NG.TypeSp a.ρ J χ) ∧
      (∀ f ∈ NG.TypeSp a.ρ J χ, ∀ f' ∈ NG.TypeSp a.ρ J χ, ∀ c : ℂ,
        NG.tN J s ϖ k (c • f + f') = c • NG.tN J s ϖ k f + NG.tN J s ϖ k f') ∧
      (∀ (s' : SplitPlace L) (ϖ' : s'.v.adicCompletion (maximalRealSubfield L)) (k' : ℕ),
        s'.v ∉ B → IsUnif L s'.v ϖ' → 1 ≤ k' → k' ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ,
          NG.tN J s ϖ k (NG.tN J s' ϖ' k' f) = NG.tN J s' ϖ' k' (NG.tN J s ϖ k f)) ∧
      (∀ f ∈ NG.TypeSp a.ρ J χ, f ≠ 0 → ∀ μ : ℂ, NG.tN J s ϖ k f = μ • f →
        ∀ l : ℕ, l.Prime → ¬ s.Above l → ∃ d : ℕ, ¬ l ∣ d ∧ IsIntegral ℤ ((d : ℂ) * μ))

end Formalism.L2
