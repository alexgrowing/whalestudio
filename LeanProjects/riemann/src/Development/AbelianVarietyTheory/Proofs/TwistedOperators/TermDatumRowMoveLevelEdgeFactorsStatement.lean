import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TermDatumRowMoveLevelEdgeFactors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termDatum_rowMove_level_edgeFactors : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} (β : CosFam G t) {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → ∀ (w : locPl G t) (j : ℕ), j + 1 < D.R.m →
    ∀ (κ : GL (Fin ((locGrid G t w.1).rank (j + 1, (locGrid G t w.1).m))) (Kw w.1)), κ ∈ givenLevel G t w.1 (j + 1, D.R.m) →
    ∀ (x : ColArgs (locGrid G t w.1)) (y : RowArgs (locGrid G t w.1)),
    ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m) κ))).prod *
      (S.term t Φ β w).datum x (Function.update (Function.update y j (y j * κ.val)) (j + 1) (κ⁻¹.val * y (j + 1))) =
    (S.term t Φ β w).datum x y := by
  first | exact @GlobalTheory.FlatRowMove.term_datum_move | exact GlobalTheory.FlatRowMove.term_datum_move | (intros; apply GlobalTheory.FlatRowMove.term_datum_move <;> assumption)
