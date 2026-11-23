import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFeCyc

noncomputable section

open Matrix GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ}

theorem longElt_corner_eq_cyc (m : ℕ) :
    longElt (m + 1) (ZMod g) * corner (longElt m (ZMod g)) = cyc g (m + 1) := by
  apply Units.ext
  ext i k
  rw [Units.val_mul, DzRed.longElt_mul_apply]
  show _ = if i = finRotate (m + 1) k then (1 : ZMod g) else 0
  have hrv : ((Fin.rev i : Fin (m + 1)) : ℕ) = m - i := by rw [Fin.val_rev]; omega
  have hil := i.isLt
  rcases Fin.eq_castSucc_or_eq_last (Fin.rev i) with ⟨d, hd⟩ | hd
  · rw [hd]
    have hdv : (d : ℕ) = m - i := by rw [← hrv, hd, Fin.coe_castSucc]
    have hdl := d.isLt
    rcases Fin.eq_castSucc_or_eq_last k with ⟨c, rfl⟩ | rfl
    · rw [DzRed.corner_cs_cs, DzRed.val_longElt]
      have hc : ((finRotate (m + 1) c.castSucc : Fin (m + 1)) : ℕ) = c + 1 := by
        rw [finRotate_succ_apply, Fin.val_add_one, if_neg (Fin.castSucc_lt_last c).ne, Fin.coe_castSucc]
      have hcl := c.isLt
      by_cases h : c = d.rev
      · rw [if_pos h, if_pos]
        ext
        rw [hc]
        have := congrArg Fin.val h
        rw [Fin.val_rev] at this
        omega
      · rw [if_neg h, if_neg]
        intro e
        apply h
        ext
        have := congrArg Fin.val e
        rw [hc] at this
        rw [Fin.val_rev]
        omega
    · rw [DzRed.corner_cs_last, if_neg]
      intro e
      have := congrArg Fin.val e
      rw [finRotate_succ_apply, Fin.last_add_one, Fin.val_zero] at this
      omega
  · rw [hd]
    have hi0 : (i : ℕ) = 0 := by
      have := congrArg Fin.val hd
      rw [hrv, Fin.val_last] at this
      omega
    rcases Fin.eq_castSucc_or_eq_last k with ⟨c, rfl⟩ | rfl
    · rw [DzRed.corner_last_cs, if_neg]
      intro e
      have := congrArg Fin.val e
      rw [finRotate_succ_apply, Fin.val_add_one, if_neg (Fin.castSucc_lt_last c).ne, Fin.coe_castSucc] at this
      omega
    · rw [DzRed.corner_last_last, if_pos]
      ext
      rw [finRotate_succ_apply, Fin.last_add_one, Fin.val_zero, hi0]

theorem exists_corner [Fact g.Prime] {m : ℕ} (M : GL (Fin (m + 1)) (ZMod g))
    (hr : ∀ l, (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)) (Fin.last m) l = if l = Fin.last m then 1 else 0)
    (hc : ∀ i, (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)) i (Fin.last m) = if i = Fin.last m then 1 else 0)
    (hlow : ∀ i l : Fin m, i < l → (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)) i.castSucc l.castSucc = 0) :
    ∃ b : GL (Fin m) (ZMod g), (∀ i l : Fin m, i < l → (b : Matrix (Fin m) (Fin m) (ZMod g)) i l = 0) ∧
      corner b = M := by
  have hne : ∀ j : Fin m, j.castSucc ≠ Fin.last m := fun j => (Fin.castSucc_lt_last j).ne
  set A : Matrix (Fin m) (Fin m) (ZMod g) :=
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)).submatrix Fin.castSucc Fin.castSucc with hA
  have he : ((-1 : ZMod g) ^ (m + m)) = 1 := by rw [← two_mul, pow_mul]; simp
  have hdet : (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)).det = A.det := by
    rw [Matrix.det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]
    simp [hr, hne, Fin.succAbove_last, A, he]
  have hAd : A.det ≠ 0 := by
    rw [← hdet]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hAd, fun i l hil => hlow i l hil, ?_⟩
  apply Units.ext
  ext i l
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last l with ⟨l, rfl⟩ | rfl
  · rw [DzRed.corner_cs_cs]; rfl
  · rw [DzRed.corner_cs_last, hc, if_neg (hne i)]
  · rw [DzRed.corner_last_cs, hr, if_neg (hne l)]
  · rw [DzRed.corner_last_last, hr, if_pos rfl]

end DiscreteGroups.sglob.DzFe
