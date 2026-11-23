import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterSpaces.HasInfCharGLSpace
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.F.LemDd

def InfUniq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)) (τ : E →+* ℂ)
  (m m' : Multiset ℂ), V ≠ ⊥ → HasInfCharGL V τ m → HasInfCharGL V τ m' → m = m'

def InfParts : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : PositivityTheory.Rg.BcB.F.Pre E N)
  (τ : E →+* ℂ), t.Good → t.Untw → TreeParts t P → t.InfOf τ (∑ i, P.m i τ)

def PairNe : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (U₁ : Submodule ℂ (Sm E a))
  (U₂ : Submodule ℂ (Sm E b)) (G : PositivityTheory.Rg.BcB.E.H E a b → ℂ), G ∈ pairSpace U₁ U₂ → G ≠ 0 → U₁ ≠ ⊥ ∧ U₂ ≠ ⊥

def LemD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : PositivityTheory.Rg.BcB.F.Pre E N)
  (τ : E →+* ℂ) (m : Multiset ℂ), t.Good → t.Untw → TreeParts t P → HasInfCharGL t.space τ m → t.space ≠ ⊥ →
    ∑ i, P.m i τ = m

theorem lemD_of (h1 : InfUniq) (h2 : InfParts) (h3 : InfTree) : LemD := by
  intro E _ _ _ N t P τ m hg hu hp hm h0
  exact h1 E N t.space τ _ _ h0 (h3 E N t τ _ (h2 E N t P τ hg hu hp)) hm

end PositivityTheory.Rg.BcB.F.LemDd

end
