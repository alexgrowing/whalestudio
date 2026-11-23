import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceIdempotentCmEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsStandardChainDataStatement
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComparisonDataStepsNonReferenceTupleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComparisonDataStepsUpToRankStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.KerOne

theorem levels_cls_cmp_at_served : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
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
      ∃ (Lv : G.Levels (Fl u v hg))
        (clsS : ∀ j, Lv.compS j → ((Fl u v hg).Pj (j + 1)).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls (j + 1))
        (up : Formalism.L2.G.Cmp.CmpUp t.cmp (w.tw Z) u v hg Lv),
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ (a a' : Lv.compS j) (L L' : ((Fl u v hg).Pj (j + 1)).Tup),
          ((Fl u v hg).Pj (j + 1)).IsLatTup L → ((Fl u v hg).Pj (j + 1)).IsLatTup L' →
          (clsS j a L = clsS j a' L' ↔ a = a' ∧ ∃ γ : (Lv.levS j a).Γ, L' = (Lv.levS j a).smul γ L)) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ x, ∃ a L, ((Fl u v hg).Pj (j + 1)).IsLatTup L ∧ clsS j a L = x) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → Submodule.span ((w.D Z).gat u v hg).O
          (up.cmpS j '' ((((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).L :
            Set (((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).V)) = Lv.Int (j + 1)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  obtain ⟨Lv, I, H, hC, hX, hE0⟩ : ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
    by_cases hμ : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0
    · exact GlobalTheory.T.exists_comparisonData_steps_upTo_rank w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ
    · exact GlobalTheory.T.comparison_data_steps_non_reference_tuple w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ
  classical
  let S := Formalism.MainNotions.G.CmpJ.stepsMu H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds t.Gt
  let clsS : ∀ j, Lv.compS j → ((Fl u v hg).Pj (j + 1)).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls (j + 1) :=
    fun j a L => if hj : j + 1 ≤ (w.D Z).R.m then
      Formalism.MainNotions.G.KAat.castCls (hC j hj) (j + 1) (Formalism.MainNotions.G.KAat.clsOf (S := (I.at' j hj).st) (H.core j hj) a L)
    else (hE0 j (by omega)).elim a
  have hcls : ∀ j (hj : j + 1 ≤ (w.D Z).R.m) a L, clsS j a L =
      Formalism.MainNotions.G.KAat.castCls (hC j hj) (j + 1) (Formalism.MainNotions.G.KAat.clsOf (S := (I.at' j hj).st) (H.core j hj) a L) :=
    fun j hj a L => dif_pos hj
  refine ⟨Lv, clsS, Formalism.L2.G.Cmp.CmpUp.ofRat S.cmpS S.injS S.ratS, ?_, ?_, ?_⟩
  · intro j hj a a' L L' hL hL'
    rw [hcls j hj, hcls j hj, (Formalism.MainNotions.G.KAat.castCls_inj _ _).eq_iff]
    exact Formalism.MainNotions.G.KAat.clsOf_iff (S := (I.at' j hj).st) (H.core j hj) (hX j hj) a a' L L' hL hL'
  · intro j hj x
    obtain ⟨x0, rfl⟩ := Formalism.MainNotions.G.KAat.castCls_surj (hC j hj) (j + 1) x
    obtain ⟨a, L, hL, e⟩ := Formalism.MainNotions.G.KAat.clsOf_surj (S := (I.at' j hj).st) (H.core j hj) x0
    exact ⟨a, L, hL, (hcls j hj a L).trans (congrArg _ e)⟩
  · intro j hj
    exact S.intS (Formalism.MainNotions.G.CmpJ.descUp H t.Gt) j hj

end GlobalTheory.Mem.Top.KerOne
