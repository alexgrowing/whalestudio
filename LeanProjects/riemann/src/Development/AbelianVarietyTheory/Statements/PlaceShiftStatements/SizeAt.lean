import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SizeAt : Prop := Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows (Fm.L x i)

def SetAt : Prop := Closed FamHyp fun Fm _ => EvPt Fm fun x _ i p =>
  GlobalTheory.GLq.ESerTie (Fm.D x i) → HidaSetting (Fm.L x i) p.R.toRealDat p.F.lv2

def AtPt (Q : ChP) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm _ => EvPt Fm fun _ _ _ p =>
  ∀ (G : Grid p CF) (W : G.Weil) (n : ℕ) (a : SlopeTestRemainingChoices p G W n), a.OK → Q a.ch

theorem SetAt.atPt (h : SetAt) {Q : ChP} (hQ : Big Q) : AtPt Q := by
  obtain ⟨c, hQ⟩ := hQ
  refine ⟨c, fun CF hCF => h.imp fun {eps} Fm _ _ a => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hQ eps CF hCF
  obtain ⟨x₁, a⟩ := a
  refine ⟨max x₀ x₁, fun x hx hle i p hp G W n b hb => ?_⟩
  exact hx₀ _ (Fm.L x i) (Fm.L_eps x i) ((le_of_max_le_left hle).trans (Fm.L_x x i hx).ge) _ _ _ _ _ _ _
    (a x hx (le_of_max_le_right hle) i p hp hb.eser) b.ch hb.is b.atScale

end GlobalTheory.BigTop.Fun

end
