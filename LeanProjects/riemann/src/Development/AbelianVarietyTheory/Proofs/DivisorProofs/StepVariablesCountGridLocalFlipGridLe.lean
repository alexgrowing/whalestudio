import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

theorem varCount_le_of_rank_le {k : Type*} [Field k] (G : Grid k) (hs : 1 ≤ G.s) (N : ℕ)
    (hN : ∀ j < G.m, G.rank (G.m, j) ≤ N) : varCount G ≤ G.m * N ^ 2 := by
  unfold varCount
  have hterm : ∀ j : Fin (G.m - 1),
      Nat.card (StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j))) ≤ N ^ 2 := by
    intro j
    have hj := j.2
    refine (Finite.card_subtype_le _).trans ?_
    rw [Nat.card_prod, Nat.card_sum, Nat.card_sum]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    have h1 := topRank_add hs (G := G) (j + 1)
    have h2 := topRank_add hs (G := G) j
    have h3 := hN (j + 1) (by omega)
    have h4 := hN j (by omega)
    rw [sq]
    exact Nat.mul_le_mul (by omega) (by omega)
  calc _ ≤ ∑ _j : Fin (G.m - 1), N ^ 2 := Finset.sum_le_sum fun j _ => hterm j
    _ = (G.m - 1) * N ^ 2 := by simp
    _ ≤ G.m * N ^ 2 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)

theorem varCount_locGrid_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E),
    varCount (locGrid G t w) ≤ D.R.m * bigN D ^ 2 := by
  intro D T L sc G t w
  refine varCount_le_of_rank_le (locGrid G t w) (show 1 ≤ D.R.r + 6 by omega) _ fun j hj => ?_
  change j < D.R.m at hj
  have h1 := Nat.mul_le_mul_right D.R.t hj.le
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + D.R.m * (D.R.r + 6) ≤ D.R.k + D.R.m * (D.R.t + (D.R.r + 6) + 1)
  nlinarith

end GlobalTheory.UnfoldLoss
