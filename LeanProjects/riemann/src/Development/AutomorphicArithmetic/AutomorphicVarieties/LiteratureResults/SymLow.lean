import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.NewtonThorneSym

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.V.Lit

def SymSqQ : Prop :=
  ∀ π : TR.CuspSub ℚ 2, π.IsRegAlg → (∀ χ : HChar ℚ, χ ≠ 1 → ¬ π.Iso (π.twist χ)) →
    ∃ P : TR.CuspSub ℚ 3, P.IsRegAlg ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ α β : ℂˣ, π.HasSat w {α, β} ∧
      P.HasSat w {α ^ 2, α * β, β ^ 2}

def SymCubeQ : Prop :=
  ∀ π : TR.CuspSub ℚ 2, π.IsRegAlg → (∀ χ : HChar ℚ, χ ≠ 1 → ¬ π.Iso (π.twist χ)) →
    (∀ μ : HChar ℚ, μ ≠ 1 → μ ^ 3 = 1 → ¬ SelfTw (adSys π.HasSat) μ) →
    ∃ P : TR.CuspSub ℚ 4, P.IsRegAlg ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ α β : ℂˣ, π.HasSat w {α, β} ∧
      P.HasSat w {α ^ 3, α ^ 2 * β, α * β ^ 2, β ^ 3}

theorem SymSat.sq (h : SymSat) : SymSqQ := fun π hr hn => by
  obtain ⟨P, hP, hs⟩ := h π hr hn 2 one_le_two
  refine ⟨P, hP, hs.mono fun w ⟨α, β, h1, h2⟩ => ⟨α, β, h1, ?_⟩⟩
  have e0 : (Finset.range (2 + 1)).val = ({0, 1, 2} : Multiset ℕ) := by decide
  rw [e0] at h2
  simpa using h2

end UpperTheory.V.Lit
