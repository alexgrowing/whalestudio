import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.MoveTop
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.MoveRow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.move :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} {N : Std G U₀} (Z : Normal W N) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p →
      ∀ (d : FinDatum G t p) (x r : FinPt G (p).small) (y r' : FinPt G (p).big)
        (U : Matrix.unitaryGroup (Fin (G.V (p).small).rank) D.host.E) (U' : Matrix.unitaryGroup (Fin (G.V (p).big).rank) D.host.E),
        GlobalTheory.RatMoveJets.RatCoord _ (N.fr (p).small) r U → GlobalTheory.RatMoveJets.RatCoord _ (N.fr (p).big) r' U' →
        Z.kkMap 1 d (r * x) (r' * y) ∘ₗ rhoVr (tauE D) (wt G (p).small) (Unitary.toUnits U) =
          rhoVr (tauE D) (wt G (p).big) (Unitary.toUnits U') ∘ₗ Z.kkMap 1 d x y := by
  intro D T L sc G W U₀ N Z μ₀ hL t p hp
  cases p with
  | chi i j =>
    obtain ⟨hi, hj⟩ := hp
    subst hj
    exact UpperTheory.WildA.moveRow Z hL t i (by omega)
  | mu t' i j => exact hp.elim
  | core i => exact hp.elim
  | top t' j => exact UpperTheory.WildA.moveTop Z hL t t' j hp
