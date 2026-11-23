import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnTypeTwistDatumEqGivenFunction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_column_type_twist_datum_eq_given_function : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) {e e' : AE D}, IsIdemSum e (locPl G t) → IsIdemSum e' (GlobalTheory.FlipTop.topPl L t) → (∀ w ∈ locPl G t, w ∉ GlobalTheory.FlipTop.topPl L t → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (Φ : G.Datum) (j : ℕ) (hj : j < D.R.m),
    GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True)) (GlobalTheory.FlipTop.topFn B t e' j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) =
      GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) := by
  first | exact @GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn | exact GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn | (intros; apply GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn <;> assumption)
