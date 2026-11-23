import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LastSeeSaw

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']

def BiForm (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (FA : GlobalTheory.LocMod.Frame k A.rank n')
    (FS : GlobalTheory.LocMod.Frame k S.rank n) (FA' : GlobalTheory.LocMod.Frame k A'.rank n'') (Ξ : SB (Matrix n n' k × Matrix n'' n k))
    (C : WO A S → WO S A' → ℂ) : Prop :=
  ∃ Λ, p.IsBiModel ψ FA FS FA' Λ ∧ C = Λ Ξ

def BiOne (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (FA : GlobalTheory.LocMod.Frame k A.rank n')
    (FS : GlobalTheory.LocMod.Frame k S.rank n) (FA' : GlobalTheory.LocMod.Frame k A'.rank n'') (C : WO A S → WO S A' → ℂ) : Prop :=
  ∃ Λ, p.IsBiModel ψ FA FS FA' Λ ∧ ∃ (O₁ : SB (Matrix n n' k)) (O₂ : SB (Matrix n'' n k))
    (O : SB (Matrix n n' k × Matrix n'' n k)), GlobalTheory.LocMod.IsOne O₁ ∧ GlobalTheory.LocMod.IsOne O₂ ∧
      (∀ q, O.1 q = O₁.1 q.1 * O₂.1 q.2) ∧ C = Λ O

def lastDat {u : D.what₂.Word} (d : Dat D u) {ι : Type} (o : OffDat d k ι) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m)
    (P₁ : Formalism.IndefR.Links.PolF D (d.st (j + 1)).V.rank (d.st j).V.rank)
    (P₂ : Formalism.IndefR.Links.PolF D d.top.st.V.rank (d.st (j + 1)).V.rank) :
    WO (D.sp.X j) (D.sp.X (j + 1)) → WO (D.sp.X (j + 1)) (D.sp.X (j + 1 + 1)) → ℂ :=
  lastBi (d.bes j 0 h).o (d.oT (j + 1 + 1) h) (o.τ j h) (xiBF d j 0 h P₁ 1) (xiTop d j h P₂)

end GlobalTheory.LastSeeSaw
end
