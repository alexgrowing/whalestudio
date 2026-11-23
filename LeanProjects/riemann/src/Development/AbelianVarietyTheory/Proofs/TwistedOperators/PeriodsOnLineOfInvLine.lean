import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def InvLine (ch : Choice R) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (S : Sizes) (P : ι → Entries S), (∀ τ, (P τ).Good) ∧
    ∃ e : PolCol ch.G × PolRow ch.G → OM P, ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
        ∃ l ∈ invFun (omRep P), ∀ Q, defPer t ch.S.toGridChoice M Q d (colFn ch a) (formTop ch t y) = l (e Q)

theorem periodsOnLine_of_invLine (hL : OneLine) (ch : Choice R) (h : InvLine ch) : PeriodsOnLine ch := by
  obtain ⟨ι, _, _, S, P, hP, e, he⟩ := h
  haveI : Module.Free ℂ (invFun (omRep P)) := Module.Free.of_divisionRing ℂ _
  obtain ⟨L0, -, hL0⟩ := finrank_eq_one_iff'.1 (hL ι S P hP)
  refine ⟨fun Q => L0.1 (e Q), fun t a hS β hβ M hM τ hτ d hd y => ?_⟩
  obtain ⟨l, hl, hle⟩ := he t a hS β hβ M hM τ hτ d hd y
  obtain ⟨c, hc⟩ := hL0 ⟨l, hl⟩
  refine ⟨c, fun Q => ?_⟩
  have hc' : c • L0.1 = l := congrArg Subtype.val hc
  rw [hle Q, ← hc']
  rfl

end GlobalTheory.RowReal

end
