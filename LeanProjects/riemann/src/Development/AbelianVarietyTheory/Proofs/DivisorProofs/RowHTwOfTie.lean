import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Formalism.LocalToGlobal.TieTwRecOf

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc

theorem row_hTw_of_tie : ∀ (Q : V4.Slot) (Lk : LkT Bundle), Row Q Lk (AtAll HasTie) → R1.TwistConditionAtBundlePoints Q Lk := by
  intro Q Lk h
  refine h.imp fun 𝒜 σ _ hT => ?_
  intro eps Fm hc x hx i
  obtain ⟨t⟩ := hT Fm hc x hx i
  exact Formalism.L2.Top4.tieTwRec_of (Q := (σ Fm hc x hx i).B.Q) t.1 (Fm.tw_supp x hx i)

end GlobalTheory.Fc
