import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameInert
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Target
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SatIndepOf

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def InertInSec : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S →
  ∀ w : Pl E, ¬ IsSplitAt w → w ∈ S

def LoneId : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (σ : SmIrr (UL n w))
  (K' : Subgroup (UL n w)), IsLevel (MonoidHom.id _) (KL n w) K' → ∀ y : fixed σ.ρ K',
    PositivityTheory.Rg.BcB.F.Eig.locOp σ K' (U.lone K') y = y

def gc (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (c : (Fin n → ℤ) →₀ ℂ) : UL n w → ℂ := fun y =>
  c.sum fun x t => t * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ) * fU n w b ϖ (lOf x) y

def ConeEig : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
  ∀ (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (q : ℕ) (σ : SmIrr (UL n w)) (α : Fin (n / 2) → ℂˣ),
    IsWitt n w b → IsUnifAt ϖ → IsUnramInv (ϖ : w.adicCompletion E) (cj w) q → IsAdmissible σ.ρ → SatUL b ϖ q σ α →
    ∃ ξ : Fin n → ℂˣ, N3.Mono ξ ∧ Finset.univ.val.map ξ = GlobalTheory.LGrp.bcParam n α ∧
      ∃ y : fixed σ.ρ (iwU n w b), y ≠ 0 ∧ ∀ c : (Fin n → ℤ) →₀ ℂ, (↑c.support ⊆ coneGL n 2) →
        PositivityTheory.Rg.BcB.F.Eig.locOp σ (iwU n w b) (gc w b ϖ c) y = evalGL c (chiN w ξ) • y

def ConeEigOf : Prop := EigInert → PositivityTheory.Rg.BcB.F.LemB.BcWeyl → ConeEig

def SatCompAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (σ : SmIrr (UL n w)) (b : GLw n w) (ϖ ϖ' : (w.adicCompletion E)ˣ) (q q' : ℕ)
    (α α' : Fin (n / 2) → ℂˣ), IsCompU π w σ → IsWitt n w b → IsUnifAt ϖ' →
    IsUnramInv (ϖ : w.adicCompletion E) (cj w) q → IsUnramInv (ϖ' : w.adicCompletion E) (cj w) q' →
    HasSatAt π w (cj w) ϖ q α → SatUL b ϖ' q' σ α' → GlobalTheory.LGrp.bcParam n α = GlobalTheory.LGrp.bcParam n α'

end PositivityTheory.Rg.BcB.F.FX

end
