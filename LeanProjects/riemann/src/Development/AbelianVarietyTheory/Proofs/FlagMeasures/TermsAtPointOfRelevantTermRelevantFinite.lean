import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FormHermitianPositive
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstT
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelPf

noncomputable section
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver

theorem terms_at_point_of_relevant : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t₀ : TauC Y u u', t₀.G ≠ 0 → t₀.relevant → ∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t₀ ∧ (∀ t : TauC Y u u', ptPN t = ptPN t₀ → t.relevant ∧ Gval (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 ≠ 0 ∧ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1)) w) ∧ (GTerm.toTerm '' {t : TauC Y u u' | ptPN t = ptPN t₀}).Finite := by
  intro D X Y u u' t₀ hG hrel
  have hrows : IsRowReps D (X.Fu u) (Y.what₂ u) := Y.rowsOK u
  have hex : ∃ v, t₀.toTerm.atPt v ∧ t₀.toTerm.relevant := by
    obtain ⟨v, hv⟩ := Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' t₀.toTerm hG hrel
    exact ⟨v, hv, hrel⟩
  have hw₀ : t₀.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf t₀.toTerm) := Formalism.L2.SG.PairVal.ptOf_spec _ hex
  refine ⟨Formalism.L2.SG.PairVal.ptOf t₀.toTerm, rfl, ?_⟩
  have key : ∀ t : TauC Y u u', ptPN t = ptPN t₀ →
      t.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf t₀.toTerm) ∧ t.toTerm.relevant := by
    intro t ht
    have hpt : Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.ptOf t₀.toTerm :=
      Formalism.L2.SG.Pf.FormRelPf.toPts_injective ht
    by_cases h : ∃ v, t.toTerm.atPt v ∧ t.toTerm.relevant
    · exact ⟨hpt ▸ Formalism.L2.SG.PairVal.ptOf_spec _ h, h.choose_spec.2⟩
    · exfalso
      have hj : Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.junkPoint D u u' := by
        unfold Formalism.L2.SG.PairVal.ptOf
        exact dif_neg h
      obtain ⟨F', -, hGv, hc⟩ := hw₀
      have he := Formalism.L2.SG.WConst.gPoint_eq_gval (lf D (X.Fu u)) F' _ hc
      rw [← hpt, hj] at he
      have hz := Formalism.L2.SG.PairVal.Gpt_junkPoint_eq_zero D u u'
      exact hGv (he.symm.trans hz)
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨hat, hr⟩ := key t ht
    have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam (hrows.1 t.lam t.mem)
    have hmk : Formalism.L2.SG.TermDef.mk t.toTerm.lam (lf D (X.Fu u)) (PD D t.toTerm.lam (lf D (X.Fu u)) u')
        (Quot.out t.toTerm.cls) = t.toTerm.cls := Quot.out_eq _
    have hA : Formalism.L2.SG.TermDef.AtPt t.toTerm.lam (lf D (X.Fu u)) (PD D t.toTerm.lam (lf D (X.Fu u)) u')
        (Formalism.L2.SG.TermDef.mk t.toTerm.lam (lf D (X.Fu u)) (PD D t.toTerm.lam (lf D (X.Fu u)) u')
          (Quot.out t.toTerm.cls)) (Formalism.L2.SG.PairVal.ptOf t₀.toTerm) := by
      rw [hmk]
      exact hat
    exact ⟨hr, (Formalism.L2.SG.TermDef.atPt_mk hTF.1 hTF.2.1 _ _).1 hA⟩
  · refine (Formalism.L2.SG.TermDef.term_atPt_finite (Formalism.L2.SG.Closed.TermsAtFinite_holds D u u') (D.sp.Y_sig 0)
      (X.Fu u) (Y.what₂ u) hrows (Formalism.L2.SG.PairVal.ptOf t₀.toTerm)).subset ?_
    rintro _ ⟨t, ht, rfl⟩
    exact (key t ht).1

end GlobalTheory.LocOver
