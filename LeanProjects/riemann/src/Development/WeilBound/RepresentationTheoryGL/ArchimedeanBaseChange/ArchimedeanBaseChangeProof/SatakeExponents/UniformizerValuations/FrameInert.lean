import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.EigInert

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Inert

def InertPlaceEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ Sec : Set (Pl E), IsSection Sec → ∀ X : Finset (Pl E), ∃ w ∈ Sec, w ∉ X ∧ ¬ IsSplitAt w ∧ IsUnramU π w

def WittEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∃ b : GLw n w, IsWitt n w b

def UnifEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w →
    ∃ (ϖ : (w.adicCompletion E)ˣ) (q : ℕ), IsUnifAt ϖ ∧ IsUnramInv (ϖ : w.adicCompletion E) (cj w) q

def SatEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (q : ℕ), IsWitt n w b → IsUnifAt ϖ →
    IsUnramInv (ϖ : w.adicCompletion E) (cj w) q → ∀ σ : SmIrr (UL n w), IsAdmissible σ.ρ → fixed σ.ρ (KL n w) ≠ ⊥ →
      ∃ α : Fin (n / 2) → ℂˣ, SatUL b (ϖ : w.adicCompletion E) q σ α

def UnifOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w →
    ∀ ϖ : (w.adicCompletion E)ˣ, IsUnifAt ϖ → ∃ q : ℕ, IsUnramInv (ϖ : w.adicCompletion E) (cj w) q

def SatUniq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ (b b' : GLw n w) (ϖ ϖ' : (w.adicCompletion E)ˣ) (q q' : ℕ) (σ : SmIrr (UL n w)) (α α' : Fin (n / 2) → ℂˣ),
    IsWitt n w b → IsWitt n w b' → IsUnifAt ϖ → IsUnifAt ϖ' → IsUnramInv (ϖ : w.adicCompletion E) (cj w) q →
    IsUnramInv (ϖ' : w.adicCompletion E) (cj w) q' → SatUL b (ϖ : w.adicCompletion E) q σ α →
    SatUL b' (ϖ' : w.adicCompletion E) q' σ α' → GlobalTheory.LGrp.WeylConjU α α'

end PositivityTheory.Rg.BcB.F.Inert

end
