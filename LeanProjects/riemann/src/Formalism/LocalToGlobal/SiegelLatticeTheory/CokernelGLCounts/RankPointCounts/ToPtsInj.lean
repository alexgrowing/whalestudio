import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SameCell

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toPts_inj {K : Type} [Zero K] {i : ℕ} (p q : Point K (i + 1)) (h : toPts p = toPts q) : p = q := by
  have key : ∀ r : Point K (i + 1),
      List.ofFn (fun a : Fin (toPts r).1.length =>
        ((toPts r).2 a, (toPts r).1.blocks.get ⟨a.1, a.2⟩)) = r.1 := by
    intro r
    apply List.ext_get
    · simp [toPts, Composition.length]
    · intro n h1 h2
      simp [toPts]
  apply Subtype.ext
  rw [← key p, ← key q, h]

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem at_ptOf (t : TauC Y u u') (hG : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t)) :
    t.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf t.toTerm) := by
  by_cases hex : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant
  · exact Formalism.L2.SG.PairVal.ptOf_spec _ hex
  · exfalso
    have hj : Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.junkPoint D u u' := by
      unfold Formalism.L2.SG.PairVal.ptOf
      rw [dif_neg hex]
    have h0 : NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t) = 0 := by
      unfold ptPN
      rw [hj]
      unfold NGPt
      obtain ⟨w0⟩ : Nonempty (InfinitePlace D.host.E) := by
        first | exact inferInstance | infer_instance
      apply Finset.prod_eq_zero (Finset.mem_univ w0)
      rw [GPt_junk]
      first | simp | rw [map_zero, mul_zero]
    linarith

end Formalism.L2.SG.NGCut.NormalVectorPairings
