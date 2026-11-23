import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.ThetaOfCsdR
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.BaseChangeIsobaricNOf

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

def preN {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (D : PositivityTheory.Rg.BcN.Datum E n) : Pre E n :=
  ⟨D.c, D.N, D.h, D.V, D.σ, D.m, D.pos, D.discrete, D.loc, D.inf⟩

def ThetaOfAsc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n),
  (∀ i, PositivityTheory.Rg.BcN.CsdAsc (D.V i)) → D.ThetaStable

def SplitSatPre : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ D D' : Pre E n, {w | IsSplitAt w ∧ ¬ D.SplitAt π w}.Finite → {w | IsSplitAt w ∧ ¬ D'.SplitAt π w}.Finite →
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ D'.Sat w B

def RThetaN : Prop := StrSat → ThetaOfAsc

theorem csdAsc_of (h1 : Strings) (h2 : CuspCsd) {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (D : Pre E n)
    (hr : D.Reg) (ht : D.ThetaStable) (i : Fin D.c) : PositivityTheory.Rg.BcN.CsdAsc (D.V i) := by
  obtain ⟨a, d, P, ha, hd, hu, hn, he⟩ := h1 E n D hr i
  have e := he P (Setoid.refl (α := CuspSub E a) P)
  exact ⟨a, d, P, hu, hn, h2 E n D hr ht i a d P ha hd hu hn e, e⟩

end PositivityTheory.Rg.BcB.F.Rig

end
