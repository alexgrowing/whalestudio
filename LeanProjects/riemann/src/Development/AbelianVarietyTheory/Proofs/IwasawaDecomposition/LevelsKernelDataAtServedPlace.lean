import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceIdempotentCmEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalCoefficientFieldEmbeddingKernelPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEmbeddingAtOrbitPositionEqInducedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalModuleLocalisingToLatticesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFreeSeriesKernelServedPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesServedPlaceEqLocalOrbitPairsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceLevelsClassesComparisonMapsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.KerOne

theorem kerData_at_served : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
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
      ∃ (Lv : G.Levels (Fl u v hg)) (KD : Formalism.L2.G.Cmp.KerData (w.D Z) t.cmp (w.tw Z) u v hg Lv),
        KD.lam = E.lam v ∧
        ThAtServed (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) E ∧
        Formalism.L2.Herm.SymmetricKernelCompatibleAtPlace t.full.1.base.toHermColsCh t.full.1.g u v hg (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) ∧
        Formalism.L2.Herm.GIwPos u v hg (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) := by
  intro K B f T w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE Fl hFl hw u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  obtain ⟨iK, hiK⟩ := GlobalTheory.T.exists_localCoefficientField_embedding_kernelPlace w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE u v hg
  have hpos := GlobalTheory.T.splitPlace_embedding_at_orbitPosition_eq_induced_alt w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE u v hg
  obtain ⟨cls0, h0iff, h0surj⟩ := GlobalTheory.T.stepZeroClasses_servedPlace_eq_localOrbitPairs w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE u v hg
  obtain ⟨Lv, clsS, up, hSiff, hSsurj, hInt⟩ := GlobalTheory.T.served_place_levels_classes_comparison_maps w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE Fl hFl hw u v hg
  classical
  let Gs := t.full.1.g
  let iwJ : ∀ j (q : Fin ((Fl u v hg).Pj j).nV), (w.D Z).host.E →+* ((Fl u v hg).Pj j).Qq q := fun j =>
    match j with
    | 0 => fun q => iw0 Gs u v hg q
    | _ + 1 => fun q => iw0 Gs u v hg q
  let globJ : ∀ j, Lv.comp j → ((Fl u v hg).Pj j).Tup →
      Submodule (𝓞 (w.D Z).host.E) (Fin (((Fl u v hg).Pj j).m + 1) → (w.D Z).host.E) := fun j =>
    match j with
    | 0 => fun _ L => if hL : ((Fl u v hg).Pj 0).IsLatTup L then
        Classical.choose (GlobalTheory.T.exists_global_module_localising_to_lattices Gs u v hg (((Fl u v hg).Pj 0).m + 1) L hL) else ⊥
    | j + 1 => fun _ L => if hL : ((Fl u v hg).Pj (j + 1)).IsLatTup L then
        Classical.choose (GlobalTheory.T.exists_global_module_localising_to_lattices Gs u v hg (((Fl u v hg).Pj (j + 1)).m + 1) L hL) else ⊥
  let clsJ : ∀ j, Lv.comp j → ((Fl u v hg).Pj j).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls j := fun j =>
    match j with
    | 0 => fun a L => cls0 a L
    | j + 1 => fun a L => clsS j a L
  let KD0 : Formalism.L2.G.Cmp.KerData (w.D Z) t.cmp (w.tw Z) u v hg Lv :=
    { fl_t := (hFl u v hg).1
      fl_m := (hFl u v hg).2
      lam := E.lam v
      iK := iK
      iLL_lam := hiK
      iw := iwJ
      glob := globJ
      glob_loc := by
        intro j _ a L hL q
        cases j with
        | zero =>
          have h := Classical.choose_spec (GlobalTheory.T.exists_global_module_localising_to_lattices Gs u v hg (((Fl u v hg).Pj 0).m + 1) L hL) q
          simp only [globJ, iwJ, dif_pos hL]
          exact h
        | succ j =>
          have h := Classical.choose_spec (GlobalTheory.T.exists_global_module_localising_to_lattices Gs u v hg (((Fl u v hg).Pj (j + 1)).m + 1) L hL) q
          simp only [globJ, iwJ, dif_pos hL]
          exact h
      cls := clsJ
      cls_iff := by
        intro j hj a a' L L' hL hL'
        cases j with
        | zero => exact h0iff a a' L L' hL hL'
        | succ j => exact hSiff j hj a a' L L' hL hL'
      cls_surj := by
        intro j hj x
        cases j with
        | zero => exact h0surj x
        | succ j => exact hSsurj j hj x
      Th := fun _ _ _ => 0
      up := up
      intS := hInt }
  obtain ⟨Th, hTh⟩ := GlobalTheory.T.exists_freeSeries_kernel_servedPlace t.Gt KD0 E rfl
  refine ⟨Lv, { KD0 with Th := Th }, rfl, hTh, ?_, ?_⟩
  · intro q x
    exact splitPlaceIdempotent_cmEmbedding_compat Gs u v hg q x
  · intro q s x
    exact hpos q s x

end GlobalTheory.Mem.Top.KerOne
