import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge

variable {eps : ℝ}

theorem f_le_k (D : D7) : (D.R.f : ℝ) ≤ D.R.k := by
  have h := D.R.f_le_k
  exact_mod_cast h

theorem k_le_r (D : D7) : (D.R.k : ℝ) ≤ D.R.r := by
  have h := D.R.two_le_m
  have h' : D.R.k ≤ D.R.r := by
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact_mod_cast h'

theorem gap_of_consec {N : ℕ} (lam : Fin N → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (h : ∀ (i : Fin N) (h : i.1 + 1 < N), G < lam i - lam ⟨i.1 + 1, h⟩) :
    ∀ (d : ℕ) (a : Fin N) (hd : a.1 + d + 1 < N), G < lam a - lam ⟨a.1 + d + 1, hd⟩ := by
  intro d
  induction d with
  | zero => intro a hd; exact h a hd
  | succ d ih =>
    intro a hd
    have h1 := ih a (by omega)
    have h2 : G < lam ⟨a.1 + d + 1, by omega⟩ - lam ⟨a.1 + (d + 1) + 1, hd⟩ := h ⟨a.1 + d + 1, by omega⟩ hd
    linarith

theorem lt_gap_of_consec {N : ℕ} (lam : Fin N → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (h : ∀ (i : Fin N) (h : i.1 + 1 < N), G < lam i - lam ⟨i.1 + 1, h⟩) (a b : Fin N) (hlt : a < b) :
    G < lam a - lam b := by
  have hab : a.1 < b.1 := hlt
  have hb := b.2
  have hd : a.1 + (b.1 - a.1 - 1) + 1 < N := by omega
  have key := gap_of_consec lam G hG h (b.1 - a.1 - 1) a hd
  have e : (⟨a.1 + (b.1 - a.1 - 1) + 1, hd⟩ : Fin N) = b :=
    Fin.ext (by show a.1 + (b.1 - a.1 - 1) + 1 = b.1; omega)
  rwa [e] at key

theorem abs_gap_of_consec {N : ℕ} (lam : Fin N → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (h : ∀ (i : Fin N) (h : i.1 + 1 < N), G < lam i - lam ⟨i.1 + 1, h⟩) (a b : Fin N) (hab : a ≠ b) :
    G < |lam a - lam b| := by
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact lt_of_lt_of_le (lt_gap_of_consec lam G hG h a b hlt) (le_abs_self _)
  · rw [abs_sub_comm]
    exact lt_of_lt_of_le (lt_gap_of_consec lam G hG h b a hlt) (le_abs_self _)

end Formalism.MainNotions.BridgeLemma

end
