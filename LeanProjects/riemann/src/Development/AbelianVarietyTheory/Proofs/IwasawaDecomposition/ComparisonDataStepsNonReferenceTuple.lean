import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Formalism.SharpRestriction.GrowthBounds.ChartRank.SiteGoodPrimeTorsion
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsCharted1AtInTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsStandardChainDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceNoChainPlaceOrTypePrimeOverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChartLevelsDeterminantMapsValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalStepBasisBaseLatticeChartsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChainChartsHyperspecialStabiliseLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChainChartLocalUnitCharacterCompatibleLeveStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

namespace GlobalTheory.Mem.Top.KerTwLv

theorem fill_of : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
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
      Formalism.MainNotions.G.CmpJ.FillTie t.Gt u v hg (Fl u v hg) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  intro x s b hb
  have h1 := hw u v hg x s (b + 1) (by simp [SizeData₂.lifts]; omega)
  apply (Rat.cast_injective (α := ℝ))
  rw [Formalism.BasicNotions.D7.hcW_e]
  have e : (((((Fl u v hg).w x (b + 1) s : ℤ) : ℚ)) : ℝ) = (((Fl u v hg).w x (b + 1) s : ℤ) : ℝ) := by push_cast; rfl
  rw [e, h1]
  unfold wj G.kaJ wG
  rw [dif_pos (by omega)]
  push_cast
  ring

theorem fin_of : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
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
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        Finite (Formalism.L2.G.compG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram
          (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Uloc ((w.D Z).what₂.places.resChar v)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt _ j hj β
  exact finite_compG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram _ _ _
    (fun x hx => ((tt.ch.lev u _ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).U_eq x).1 hx)
    (tt.ch.finite_cls u _ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β)

set_option maxHeartbeats 4000000 in

theorem cmpJ_data_ne : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0 →
      ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  intro hμ
  obtain ⟨tt, htt⟩ := GlobalTheory.T.trueColumnChoice_exists_standardChainData w.I w.ok w.pins w.l Z w.l0 nch n.tp t.C n.xi t.std t.stdLv
  have hpl := GlobalTheory.T.served_place_no_chain_place_or_type_prime_over w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  obtain ⟨dt, hdt⟩ := GlobalTheory.T.twisted_chart_levels_determinant_maps_values w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hB := GlobalTheory.T.exists_orthonormal_step_basis_base_lattice_charts w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hψ := GlobalTheory.T.exists_chainChart_localUnitCharacter_compatible_level w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hfin := fin_of w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hfill := fill_of w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  let Cd : GlobalTheory.Mem.Top.KerTwLv.ChData tt.ch t.g.herm u ((w.D Z).what₂.muAt v) v hg :=
    { B := fun j hj => (hB j hj).choose
      fr_lat := fun j hj β => (hB j hj).choose_spec.2 β
      ψ := fun j hj β => (hψ j hj β).choose
      fin := hfin }
  have hhyp := GlobalTheory.T.twisted_chain_charts_hyperspecial_stabilise_lattice w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt hpl Cd
  let Zt := Formalism.MainNotions.G.KAat.atInTw (X0 := t.g.herm) tt.forms u ((w.D Z).what₂.muAt v) hμ dt (Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1)
  have A : Formalism.MainNotions.G.ChF.HypTies Zt t.Gt t.cmp :=
    { fl_t := (hfl u v hg).1
      fill := hfill
      step := fun j hj =>
        { frRat := fun β => Cd.frRat t.Gt (Fl u v hg) (hfl u v hg).1 j hj β
          sameU := fun β => Cd.sameU tt.forms hμ t.Gt (Fl u v hg) (hfl u v hg).1 dt j hj β
          hypT := fun β => (hhyp j hj β).1
          bad_p := hpl.2.1
          std := (hB j hj).choose_spec.1
          psi := fun β => (hψ j hj β).choose_spec
          chRat := hdt j hj
          hypC := fun β => (hhyp j hj β).2
          ok := hpl.1
          siteGood_prime_torsion := hpl.2.2
          Lb_eq := fun β => Cd.Lb_eq tt.forms hμ t.Gt (Fl u v hg) (hfl u v hg).1 dt j hj β } }
  exact ⟨Cd.Lv t.Gt (Fl u v hg) (hfl u v hg).1, Zt.I t.Gt, A.hyp t.g.cmp, fun j hj => rfl,
    fun j hj => (A.atHyp t.g.cmp).chX j hj, fun j hj => Cd.empty t.Gt (Fl u v hg) (hfl u v hg).1 j hj⟩

end GlobalTheory.Mem.Top.KerTwLv
