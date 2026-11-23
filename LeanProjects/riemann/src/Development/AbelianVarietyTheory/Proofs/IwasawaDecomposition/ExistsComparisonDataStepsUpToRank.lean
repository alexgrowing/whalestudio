import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LvSite
import Formalism.SharpRestriction.GrowthBounds.ChartRank.SiteGoodPrimeTorsion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepTiesD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerMidStepChartsConditionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerTopStepChartConditionsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv Formalism.MainNotions.G.ChF Formalism.L2.G Formalism.L2.Forms

theorem fillTie_of {D : D7} (Gt : GatTies D) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) (Fl : Fills (D.gat u v hg))
    (hw : ∀ (x : Fin (D.gat u v hg).P.nV) (s : Fin ((D.gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts D,
      ((Fl.w x j s : ℝ)) = wj D j (Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ D j) : FillTie Gt u v hg Fl := by
  intro x s b hb
  have h := hw x s (b + 1) (by simp only [SizeData₂.lifts, Finset.mem_Icc]; omega)
  have e1 : wj D (b + 1) (Gt.gat_pos u v hg ⟨x, s⟩) = (((D.hc (Gt.gat_pos u v hg ⟨x, s⟩)).e ⟨b, hb⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dif_pos (by omega)]
    rfl
  rw [e1] at h
  rw [D.hcW_e]
  apply Rat.cast_injective (α := ℝ)
  unfold wG
  unfold G.kaJ at h
  push_cast
  rw [h]
  push_cast
  ring

theorem reL_reL_symm {a b : ℕ} (h : a = b) {E : Type} [Field E] [NumberField E] (L : Submodule (𝓞 E) (Fin b → E)) :
    reL h (reL h.symm L) = L := by
  subst h
  rw [reL_rfl, reL_rfl]

theorem site_of {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Gt : GatTies D) (c : LatCmp D)
    (H : ∀ i (hi : i + 1 ≤ D.R.m), ∃ (Fo : FormsIn (D.fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD X0 u w hg Fo),
      StepTiesD X0 u w hg hi Fo S c) :
    ∃ Z : SiteD X0 u w hg (D.fm u), ∀ (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (i : ℕ) (hi : i + 1 ≤ D.R.m),
      StepTies hi (Z.Fo i hi) (Z.loc Fl ht i hi) Gt c := by
  choose Fo hfin S hS using H
  refine ⟨⟨Fo, hfin, S⟩, fun Fl ht i hi => ?_⟩
  obtain ⟨hT, hC, hbad, hstd, hpsi, hch, hok, hpT⟩ := hS i hi
  exact
    { frRat := SiteD.frRat _ Fl ht i hi
      sameU := SiteD.sameU _ Fl ht i hi
      hypT := hT
      bad_p := hbad
      std := hstd
      psi := hpsi
      chRat := hch
      hypC := hC
      ok := hok
      siteGood_prime_torsion := hpT
      Lb_eq := fun β => (reL_reL_symm _ _).symm }

theorem exists_comparisonData_steps_at_baseCharacter : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
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
      have : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 →
      ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
  intro K B f T w hO hF hP Z t Wt nch hn Y hMu hQ O hStd hUnf E hE Fl hFl hW u v hg _ hμ
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  have ht : (Fl u v hg).t = (w.D Z).R.t := (hFl u v hg).1
  have hFt : FillTie t.Gt u v hg (Fl u v hg) := fillTie_of t.Gt u v hg (Fl u v hg) (hW u v hg)
  obtain ⟨S, hS⟩ := site_of t.g.herm u v hg t.Gt t.cmp (fun i hi => by
    by_cases h2 : i + 1 + 1 ≤ (w.D Z).R.m
    · exact GlobalTheory.T.memberFormsLayer_midStep_charts_conditions w hO hF hP Z t Wt nch hn Y hMu hQ O hStd hUnf E hE u v hg i hi h2
    · exact GlobalTheory.T.memberFormsLayer_topStep_chart_conditions w hO hF hP Z t Wt nch hn Y hMu hQ O hStd hUnf E hE u v hg i hi (by omega))
  have A : HypTiesI t.g.herm (S.inMem (w.tw Z) (Fl u v hg) ht t.Gt) t.Gt t.cmp :=
    ⟨ht, hFt, fun j hj => ⟨S.Fo j hj, S.loc (Fl u v hg) ht j hj, rfl, hS (Fl u v hg) ht j hj⟩⟩
  rw [hμ]
  exact ⟨S.lv (Fl u v hg) ht, S.inMem (w.tw Z) (Fl u v hg) ht t.Gt, A.hyp t.g.cmp,
    fun j hj => ((w.D Z).memberColumns_twistedChain_base u).symm, fun j hj => A.chX j hj, fun j hj => ⟨fun c => absurd c.1 (by omega)⟩⟩

end GlobalTheory.Mem.Top.KerOne.CertEq

end
