import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7}

abbrev termGramMatrix (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') : GramM D := ZhatL (X.fl t) (X.fl' t)

def wordPairGramNorm (D : D7) (u u' : D.what₂.Word) (Z : GramM D) : ℝ := ∏ τ, nV D (Tu D u) (Tu D u') Z τ

def wordPairGramProduct (D : D7) (u u' : D.what₂.Word) (Z : GramM D) : ℝ :=
  (∏ τ, Gz D (Tu D u) (Tu D u') Z τ) * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f)

def pairDeterminant (X : TermTie D) {u u' : D.what₂.Word} (p : D.s.Pair u u') : ℝ :=
  latDet (hS D) (Mlat (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) (X.fl' (D.s.psnd p)) (X.beta p) (gS D)) *
    (iIdx (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) : ℝ) *
    (iIdx (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.psnd p)) : ℝ)

def wordPairDeterminantGeOne (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ p : D.s.Pair u u', D.s.Gterm (D.s.pfst p) ≠ 0 → D.s.Gterm (D.s.psnd p) ≠ 0 → 1 ≤ pairDeterminant X p

def wordPairEntriesInLattice (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ a b : Fin (D.R.rS + 1), ∃ Λ : AddSubgroup (D.what₂.Tau → ℂ), (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) ∧
    ∀ (t : D.s.Term u u') (Z : GramM D), D.s.Gterm t ≠ 0 → D.s.relevant t → ZEquiv (termGramMatrix X t) Z →
      (fun τ => ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (Z a b)) ∈ Λ

end Defs

end Formalism.MainNotions.BridgeLemma₂

end
