import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.ArchBaseChangeOfHyp
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.Desc

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Temp (π : CG E n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, π.HasSat w B ∧ ∀ z ∈ B, ‖(z : ℂ)‖ = 1

def TempOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → Temp (CG.mk π)

def RTemp : Prop := GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.Published.JacquetShalikaRigidity → TempOf

def SplitCore : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CG E n, π.IsUnitary → Temp π →
  ∀ (J : Type) [Fintype J] (a : J → ℕ) (P : ∀ j, CG E (a j)), (∀ j, 1 ≤ a j) → (∀ j, (P j).IsUnitary) →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
      ∃ b : J → Multiset ℂˣ, (∀ j, (P j).HasSat w (b j)) ∧ π.HasSat w (∑ j, b j)) →
    ∃ j, (⟨a j, P j⟩ : Σ m, CG E m) = ⟨n, π⟩

def RSplitCore : Prop := PositivityTheory.RgJS.RSU → GlobalTheory.Published.JacquetShalikaBound → SplitCore

def SplitAll : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsUnitary → Temp (CG.mk π) → ∀ D : Pre E n, D.Reg → SplitLike D π →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B

def RSplitAll : Prop := SplitCore → Rig.StrSat → Strings → SplitAll

def UnitOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → (CG.mk π).IsUnitary

def RunDesc2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
    (∃ σ, WeakDesc σ π) ∨ ∃ D : Pre E n, D.Reg ∧ SplitLike D π ∧ ¬ IsOne D π

end PositivityTheory.Rg.BcB.Desc

end
