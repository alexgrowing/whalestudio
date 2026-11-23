import Formalism.LocalToGlobal.Columns.TopInvHolds
import Formalism.LocalToGlobal.Columns.RecLevelSym
import Formalism.LocalToGlobal.Columns.LevGCount

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section LR

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem xt_N_top {m2 : ℕ} (hm : R.m = m2 + 2) : R.N (m2 + 1 + 1) - 1 = R.r + R.m * R.t := by
  unfold Ranks.N Ranks.r
  rw [hm]
  have e : (m2 + 1 + 1) * (R.t + 1) = (m2 + 2) * R.t + (m2 + 2) := by ring
  omega

theorem lastRow_colLevSym (Ch : Chars X Pr R.m) {m2 : ℕ} (hm : R.m = m2 + 2) : LastRow (colLevSym Ch (m2 + 1 + 1)) := by
  intro w h' hh' l
  rw [colLevSym_top_H Ch (by omega) w] at hh'
  have hN := xt_N_top (R := R) hm
  have hbt := HPar_le _ _ _ hh'.1
  by_cases hl : l.1 = R.N (m2 + 1 + 1) - 1
  · rw [if_pos hl, hh'.2 _ l (by rw [hl, hN])]
    have : (⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ : Fin (R.N (m2 + 1 + 1))) = l := Fin.ext hl.symm
    rw [this, Matrix.one_apply_eq]
  · rw [if_neg hl]
    refine mem_btG.1 hbt _ l ?_
    have hl2 : l.1 < R.r + R.m * R.t := by have := l.2; omega
    show coarse R.r (List.replicate R.m R.t) l.1 < coarse R.r (List.replicate R.m R.t) (R.N (m2 + 1 + 1) - 1)
    rw [hN]
    have e1 : coarse R.r (List.replicate R.m R.t) (R.r + R.m * R.t) = R.m + 1 := by
      unfold coarse blkIdx
      rw [if_neg (by omega), Nat.add_sub_cancel_left, blkIdx_replicate_of_le _ _ _ le_rfl]
    rw [e1]
    unfold coarse blkIdx
    split_ifs with h0
    · omega
    · have := blkIdx_replicate_lt R.t R.m (l.1 - R.r) (by omega)
      omega

end LR

end Formalism.L2.Col
