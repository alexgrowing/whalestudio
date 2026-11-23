import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FittedTiesBoundEventualStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop

namespace GlobalTheory.BigTop.Fun

theorem halfRank_eq_sqRank_div (D : D7) (ij : Sq D) :
    GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 = sqRank D ij / 2 := by
  unfold GlobalTheory.FunObj.SqNum.halfRank sqRank
  congr 1
  simp only [GlobalTheory.ChiGrid.rankV]
  ring

theorem den_tie : SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) →
    DenSum → Den @Comparison₂ := by
  intro hS hL hD
  refine Lf.mono (GlobalTheory.T.fitted_ties_bound_eventual _ hS hL hD) fun {D _ _ _ _ _ _ _ _ _} p CF d C CH _ hd => ⟨hd, fun hq => ?_⟩
  obtain ⟨-, a, ha⟩ := hd
  have hsq := ha.sq
  refine ⟨fun l hl => ((hsq.den l).1 hl).1, fun ij s h1 h2 => ?_⟩
  lift s to ℕ using (by omega)
  have h1' : 1 ≤ s := by exact_mod_cast h1
  have h2' : s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by
    have h2'' : s ≤ sqRank D ij / 2 := by exact_mod_cast h2
    exact h2''.trans_eq (halfRank_eq_sqRank_div D ij).symm
  exact hq ij.1 ij.2 s h1' h2' _ (hsq.inside ij s h1' h2').2 d.Sd fun l hl => ((hsq.den l).1 hl).1

end GlobalTheory.BigTop.Fun

end
