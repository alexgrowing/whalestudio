import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCOfOcc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GflagSwap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem leadingMinor_eq_pointMinor {D : D7} {n : ℕ} (w : Point D.host.E n) (l : ℕ) (hl : l ≤ n) :
    Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (ptMat w) l = Formalism.MainNotions.S.LocalSplitGroups.Dmin w l := by
  unfold Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor Formalism.MainNotions.S.LocalSplitGroups.Dmin
  rw [dif_pos hl]
  let e : Fin l ≃ {i : Fin n // (i : ℕ) < l} :=
    { toFun := fun j => ⟨Fin.castLE hl j, by simp⟩
      invFun := fun i => ⟨i.1, i.2⟩
      left_inv := fun j => by ext; simp
      right_inv := fun i => by ext; simp }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem conjF_star' {D : D7} (x : D.host.E) : D.conjF x = star x :=
  (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host) x).symm

theorem GPt_junk (D : D7) (u u' : D.what₂.Word) :
    GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) (toPts (Formalism.L2.SG.PairVal.junkPoint D u u')) = 0 := by
  have h := (Formalism.MainNotions.S.Inh.zero_of_gram_point_exists D u u').choose_spec
  unfold Formalism.MainNotions.S.LocalSplitGroups.Gpt at h
  unfold Formalism.L2.SG.PairVal.junkPoint GPt
  rw [LeadingMinorIntegrality.dlast_eq, LeadingMinorIntegrality.dr_eq, leadingMinor_eq_pointMinor _ _ le_rfl, leadingMinor_eq_pointMinor _ _ (Nat.le_succ _),
    ← conjF_star', ← conjF_star']
  convert h using 3
  all_goals first
    | rfl
    | (push_cast; rfl)
    | norm_cast

theorem GPt_ne_of_NGPt {D : D7} (TT : ℕ) (γ : PN.Pts D.host.E D.R.rS) (h : 1 ≤ NGPt D.host.rdE TT γ) :
    GPt TT γ ≠ 0 := by
  unfold NGPt at h
  intro h0
  rw [h0] at h
  simp [Fintype.card_ne_zero] at h
  linarith

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem gval_occ (t : TauC Y u u')
    (hG : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t)) :
    Gval (lf D (X.Fu u)) t.frame = GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t) := by
  have hne := GPt_ne_of_NGPt _ _ hG
  by_cases h : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant
  · obtain ⟨F', ⟨hP, hmk⟩, -, hcell⟩ := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm h
    have h1 := LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) F' _ hcell
    rw [show ptPN t = toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) from rfl, h1, ← Formalism.L2.SG.Pf.SatGram.gterm_G Y t]
    have hΛ := (Y.rowsOK u).1 t.lam t.mem
    show Formalism.L2.SG.TermDef.Gt _ _ _ t.toTerm.cls = _
    rw [← hmk]
    exact Formalism.L2.SG.TermDef.Gt_mk ((Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).1) _
  · exfalso
    apply hne
    show GPt _ (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) = 0
    unfold Formalism.L2.SG.PairVal.ptOf
    rw [dif_neg h]
    exact GPt_junk D u u'

end Formalism.L2.SG.NGCut.NormalVectorPairings
