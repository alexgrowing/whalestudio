import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalStepBasisBaseLatticeCharts
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_step_basis_base_lattice_charts : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m), ∃ B : GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w.D Z).host.E,
        cT (sigD (w.D Z) : (w.D Z).host.E →+* (w.D Z).host.E)
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 * gramN (w.D Z) (j + 1) hj *
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 = 1 ∧
        ∀ (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)) w' h (x : Fin ((w.D Z).sp.X (j + 1)).rank → w'.adicCompletion (w.D Z).host.F),
          (∃ y ∈ Formalism.L2.Herm.locL w' (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb,
            ∀ a, ((t.g.herm.g u v hg).spl w' h (y a)).1 = x a) ↔
          ∀ a, (((GlobalTheory.Mem.Top.KerTwLv.frOf t.g.herm u v hg B w' h)⁻¹ :
            GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)) :
              Matrix (Fin ((w.D Z).sp.X (j + 1)).rank) (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)).mulVec x a ∈
            w'.adicCompletionIntegers (w.D Z).host.F := by
  first | exact @GlobalTheory.Mem.Top.KerTwLv.stepBasis_std | exact GlobalTheory.Mem.Top.KerTwLv.stepBasis_std | (intros; apply GlobalTheory.Mem.Top.KerTwLv.stepBasis_std <;> assumption)
