import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameInert
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FieldNOf

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.LemB

def CjEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
  ∀ s : w.adicCompletion E →+* w.adicCompletion E,
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → s = cj w

def SatIndep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (ϖ ϖ' : w.adicCompletion E) (q q' : ℕ) (α α' : Fin (n / 2) → ℂˣ),
    IsUnramInv ϖ (cj w) q → IsUnramInv ϖ' (cj w) q' → HasSatAt π w (cj w) ϖ q α → HasSatAt π w (cj w) ϖ' q' α' →
    GlobalTheory.LGrp.bcParam n α = GlobalTheory.LGrp.bcParam n α'

def BcWeyl : Prop := ∀ (n : ℕ) (α α' : Fin (n / 2) → ℂˣ), GlobalTheory.LGrp.WeylConjU α α' →
  GlobalTheory.LGrp.bcParam n α = GlobalTheory.LGrp.bcParam n α'

def SatIndepOf : Prop := PositivityTheory.Rg.BcB.F.Inert.SatUniq → BcWeyl → SatIndep

end PositivityTheory.Rg.BcB.F.LemB

end
