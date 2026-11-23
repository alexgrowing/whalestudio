import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.LoopTieOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y}

def FrameEqvInj (T : TermTie D) {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS (Tu D u : D.host.E)) : Prop :=
  ∀ t t' : D.s.Term u u', T.abelian₂ t = T.abelian₂ t' →
    (∃ n ∈ NLam (T.abelian₂ t) (lf D F0), FrameEqv D n (T.fl' t) (T.fl' t')) → t = t'

theorem pair_eq_of_terms (hI : SIso D.s (sOf hF)) {u u' : D.what₂.Word} (p q : D.s.Pair u u') (h1 : D.s.pfst p = D.s.pfst q)
    (h2 : D.s.psnd p = D.s.psnd q) : p = q := by
  apply (hI.eP u u').injective
  apply Subtype.ext
  apply Prod.ext
  · have e : (sOf hF).pfst (hI.eP u u' p) = (sOf hF).pfst (hI.eP u u' q) := by
      rw [← hI.pfst, ← hI.pfst, h1]
    exact e
  · have e : (sOf hF).psnd (hI.eP u u' p) = (sOf hF).psnd (hI.eP u u' q) := by
      rw [← hI.psnd, ← hI.psnd, h2]
    exact e

theorem pairInj_of (hI : SIso D.s (sOf hF)) (T : TermTie D) {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS (Tu D u : D.host.E))
    (hTI : FrameEqvInj T (u' := u') F0) :
    ∀ p q : D.s.Pair u u', T.abelian₂ (D.s.pfst p) = T.abelian₂ (D.s.pfst q) →
      (∃ n' ∈ NLam (T.abelian₂ (D.s.pfst p)) (lf D F0), ∃ n'' ∈ NLam (T.abelian₂ (D.s.pfst p)) (lf D F0),
        FrameEqv D n' (T.fl' (D.s.pfst p)) (T.fl' (D.s.pfst q)) ∧
        FrameEqv D n'' (T.fl' (D.s.psnd p)) (T.fl' (D.s.psnd q)) ∧
        ∀ x ∈ orth (hS D) (Xsp (T.fl' (D.s.pfst q))),
          T.beta q x - n'' (T.beta p (n'.symm x)) ∈ Xsp (T.fl' (D.s.psnd q))) → p = q := by
  rintro p q hL ⟨n', hn', n'', hn'', h1, h2, -⟩
  have e1 : D.s.pfst p = D.s.pfst q := hTI _ _ hL ⟨n', hn', h1⟩
  have e2 : D.s.psnd p = D.s.psnd q := by
    apply hTI
    · rw [← T.pLam p, ← T.pLam q, hL]
    · refine ⟨n'', ?_, h2⟩
      rw [← T.pLam p]
      exact hn''
  exact pair_eq_of_terms hI p q e1 e2

end Gen

section AtTermTieOf

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))

def loopRowsOf (H : TieHyp W hI) (A : AmpDat X) (hV : PvalForm W hI A) (hRR : RowRepsIso D) (u u' : D.what₂.Word)
    (hTI : FrameEqvInj (termTieOf W hI H A hV) (u' := u') (FlagOfWord W u)) :
    LoopRowsDat D (termTieOf W hI H A hV) u u' where
  F0 := FlagOfWord W u
  flag_e_eq_hyperbolic := F0rec_e W u
  formsAtZero := F0rec_z_eq_zmOf W u
  what₂ := rowsRec W Y u
  isRows := hRR (W.δ u) (W.isom u) (X.Fu u) (Y.what₂ u) (Y.rowsOK u)
  fl_eq := fun _ => rfl
  Lam_mem := fun t => lamOf_mem W hI t
  frame_ok := fun t => (pdC W hI t).2.2
  wRow_eq := fun _ => rfl
  pair_inj := pairInj_of hI _ (FlagOfWord W u) hTI

end AtTermTieOf

section Inhab

theorem parts_nonempty_of_noTerms (D : D7) (large₂ : SizeData₂ D) (T : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (h : IsEmpty (D.s.Term u u')) (hR : Formalism.MainNotions.S.Inh.tie_HRows D u) (hA : Formalism.MainNotions.S.Inh.tie_HAmp D large₂ u u' C1) :
    Nonempty (LoopRowsDat D T u u') ∧ ∃ B : LoopLocDat D large₂ u u' C1, Nonempty (LoopTermDat D large₂ T u u' C1 B) := by
  obtain ⟨L⟩ := Formalism.MainNotions.S.Inh.tie_loopTie_of_noTerms D large₂ T u u' C1 h hR hA
  refine ⟨⟨⟨L.F0, L.flag_e_eq_hyperbolic, L.formsAtZero, L.what₂, L.isRows, L.fl_eq, L.Lam_mem, L.frame_ok, L.wRow_eq, L.pair_inj⟩⟩,
    ⟨L.θ, L.θ_win, L.W, L.goodW, L.A, L.goodS, L.deg_eq⟩, ⟨?_⟩⟩
  exact ⟨L.γ, L.pt, L.θR, L.νR, L.volR, L.volR_pos, L.gram, L.rel, L.J_irr, L.J_norm⟩

end Inhab

end Formalism.L2.SG.LoopTieOf
