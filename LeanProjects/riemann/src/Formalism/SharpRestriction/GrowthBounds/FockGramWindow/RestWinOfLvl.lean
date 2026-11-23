import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.LvlDef
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfMinimalVector
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FockKSmulRight

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.MainNotions.G.SymmetricFormBlocks

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestWinNum (CM : ℝ) : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b → ∀ J : ℕ,
    J ≤ (X.S C0 CE1 CE2).bPlus →
    b.oPlus ≤ X.L.a ∧ 0 ≤ X.L.Y * D1r C0 CE1 CE2 X CM ∧
    ∃ h : ℕ, X.winA.card ≤ X.p ^ h ∧ J + 1 ≤ X.p ^ h ∧
      (J : ℝ) / X.winA.card +
        (((x0N X.p (aBig X) X.r (2 * X.s + 1) (X.S C0 CE1 CE2).t : ℝ) + (⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) + lgN X.p (aBig X) X.r) +
          (J : ℝ) * h / X.winA.card) / (((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1) ≤ 5 / X.L.Y

variable {C0 CE1 CE2 X}

theorem restWin_of_lvl {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (CM : ℝ) (hL : WinLvl) (hN : RestWinNum C0 CE1 CE2 X CM)
    (haw : X.L.a ∈ X.winA) :
    RestWin C0 CE1 CE2 X CM := by
  classical
  haveI : NeZero X.r := ⟨X.hm⟩
  intro dl hdl aTop haTop x hx n₁ e he hli horth hdiag
  have haTop' : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) := by
    unfold cbox at haTop
    exact (Finset.mem_filter.mp haTop).1
  unfold idx at hx
  rw [Finset.mem_sigma] at hx
  have hK : Kept X.p X.r (X.S C0 CE1 CE2) aTop x.fst :=
    (mem_keptSet _ _ _ _ _).mp (Finset.mem_filter.mp hx.1).1
  have hlv : x.snd ∈ levels (gB C0 CE1 CE2 X aTop 0 x.fst) := hx.2
  unfold levels at hlv
  have hLOK : (gB C0 CE1 CE2 X aTop 0 x.fst).LevelOK x.snd.1 x.snd.2 :=
    (Finset.mem_filter.mp hlv).2
  have hJ : JN (gB C0 CE1 CE2 X aTop 0 x.fst) x.snd.2 ≤ (X.S C0 CE1 CE2).bPlus :=
    le_trans (min_le_right _ _) (Nat.sub_le _ _)
  obtain ⟨hob, hYD, h, hWh, hJh, hineq⟩ := hN aTop haTop' x.fst hK _ hJ
  obtain ⟨hA1, hdeg, hB, hz, -⟩ :=
    gB_deg_le C0 CE1 CE2 X hCYb hCE1 hCE2 hH aTop haTop' X.L.a haw x.fst hK
  have hW : 0 < X.winA.card := Finset.card_pos.mpr ⟨_, haw⟩
  have hk : 0 ≤ ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ := Int.floor_nonneg.mpr hYD
  have hmain := hL X.p (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.fst) (gB_blockOK _ _ _ _ _ _ _)
    x.snd.1 x.snd.2 hLOK (aBig X) hA1 hdeg hB hz n₁ e he hli horth ⌊D1r C0 CE1 CE2 X CM⌋ hdiag
    (X.L.a - x.fst.oPlus) X.winA.card h _ hk hW hWh hJh
  have hbe : ∀ (aPlus z : ℕ), aPlus - x.fst.oPlus = z →
      bejj (r := X.r) X.p (gB C0 CE1 CE2 X aTop aPlus x.fst) x.snd.1 x.snd.2 =
        bejj (r := X.r) X.p (setZ (gB C0 CE1 CE2 X aTop 0 x.fst) z) x.snd.1 x.snd.2 := by
    rintro aPlus z rfl
    rfl
  rw [winA_sum]
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))) (le_trans hmain ?_)
  · rw [hbe (X.L.a + i) (X.L.a - x.fst.oPlus + i) (by omega)]
    rfl
  · rw [mul_comm (5 / X.L.Y)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_left hineq (Nat.cast_nonneg _)

end Formalism.MainNotions.G.GramWindowAlt

end
