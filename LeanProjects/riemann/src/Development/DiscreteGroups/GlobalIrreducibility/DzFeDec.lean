import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFeMat

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

theorem rot_symm_zero : (finRotate (m + 1)).symm 0 = Fin.last m := by
  rw [Equiv.symm_apply_eq, finRotate_last]

theorem rot_castSucc (l : Fin m) : finRotate (m + 1) (Fin.castSucc l) = Fin.succ l := by
  ext
  rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last l).ne]
  simp

theorem rot_symm_val (i : Fin (m + 1)) (hi : i ≠ 0) : (((finRotate (m + 1)).symm i : Fin (m + 1)) : ℕ) + 1 = i := by
  obtain ⟨k, rfl⟩ := (finRotate (m + 1)).surjective i
  rw [Equiv.symm_apply_apply]
  have hk : k ≠ Fin.last m := fun h => hi (by rw [h, finRotate_last])
  rw [coe_finRotate_of_ne_last hk]

theorem rot_symm_ne_last (i : Fin (m + 1)) (hi : i ≠ 0) : (finRotate (m + 1)).symm i ≠ Fin.last m := fun h =>
  hi ((finRotate (m + 1)).symm.injective (h.trans rot_symm_zero.symm))

theorem cyc_val : ((cyc g (m + 1) : Gn g (m + 1)) : Mt g (m + 1)) =
    Matrix.of fun i k => if i = finRotate (m + 1) k then 1 else 0 := rfl

theorem cyc_inv_val : (((cyc g (m + 1))⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) =
    Matrix.of fun i k => if finRotate (m + 1) i = k then 1 else 0 := rfl

theorem cyc_mul_apply (Z : Mt g (m + 1)) (i k : Fin (m + 1)) :
    ((cyc g (m + 1) : Gn g (m + 1)) * Z : Mt g (m + 1)) i k = Z ((finRotate (m + 1)).symm i) k := by
  rw [cyc_val, Matrix.mul_apply, Finset.sum_eq_single ((finRotate (m + 1)).symm i)]
  · simp
  · intro l _ hl
    rw [Matrix.of_apply, if_neg (fun h => hl (by rw [h, Equiv.symm_apply_apply])), zero_mul]
  · simp

theorem mul_cycinv_apply (Z : Mt g (m + 1)) (i k : Fin (m + 1)) :
    (Z * (((cyc g (m + 1))⁻¹ : Gn g (m + 1)) : Mt g (m + 1))) i k = Z i ((finRotate (m + 1)).symm k) := by
  rw [cyc_inv_val, Matrix.mul_apply, Finset.sum_eq_single ((finRotate (m + 1)).symm k)]
  · simp
  · intro l _ hl
    rw [Matrix.of_apply, if_neg (fun h => hl (by rw [← h, Equiv.symm_apply_apply])), mul_zero]
  · simp

theorem cycinv_mul_apply (Z : Mt g (m + 1)) (l k : Fin (m + 1)) :
    ((((cyc g (m + 1))⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) * Z) l k = Z (finRotate (m + 1) l) k := by
  rw [cyc_inv_val, Matrix.mul_apply, Finset.sum_eq_single (finRotate (m + 1) l)]
  · simp
  · intro a _ ha
    rw [Matrix.of_apply, if_neg (Ne.symm ha), zero_mul]
  · simp

def Hp (r : Fin (m + 1) → ZMod g) : Mt g (m + 1) :=
  Matrix.of fun i k => if i = Fin.last m then r k else (1 : Mt g (m + 1)) i k

theorem hp_lower (r : Fin (m + 1) → ZMod g) : (Hp r : Mt g (m + 1)).BlockTriangular OrderDual.toDual := by
  intro i k hik
  have h : i < k := hik
  have hi : i ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le h (Fin.le_last k))
  simp [Hp, hi, Matrix.one_apply_ne (ne_of_lt h)]

theorem det_hp (r : Fin (m + 1) → ZMod g) : (Hp r : Mt g (m + 1)).det = r (Fin.last m) := by
  rw [Matrix.det_of_lowerTriangular _ (hp_lower r), Fin.prod_univ_castSucc]
  simp [Hp, (Fin.castSucc_lt_last _).ne]

def hpGL (r : Fin (m + 1) → ZMod g) (hr : r (Fin.last m) ≠ 0) : Gn g (m + 1) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Hp r) (by rw [det_hp]; exact hr)

theorem hpGL_val (r : Fin (m + 1) → ZMod g) (hr : r (Fin.last m) ≠ 0) :
    ((hpGL r hr : Gn g (m + 1)) : Mt g (m + 1)) = Hp r := rfl

abbrev WIdx (m j : ℕ) := {k : Fin (m + 1) // j < (k : ℕ) ∧ (k : ℕ) < m}

def rvec (j : ℕ) (t : (ZMod g)ˣ) (w : WIdx m j → ZMod g) : Fin (m + 1) → ZMod g :=
  fun k => if k = Fin.last m then (t : ZMod g) else if h : j < (k : ℕ) ∧ (k : ℕ) < m then w ⟨k, h⟩ else 0

theorem rvec_last (j : ℕ) (t : (ZMod g)ˣ) (w : WIdx m j → ZMod g) : rvec j t w (Fin.last m) = t := by
  simp [rvec]

theorem rvec_low {j : ℕ} (hj : j < m) (t : (ZMod g)ˣ) (w : WIdx m j → ZMod g) (k : Fin (m + 1))
    (hk : (k : ℕ) ≤ j) : rvec j t w k = 0 := by
  have hk' : k ≠ Fin.last m := fun h => by
    rw [h, Fin.val_last] at hk
    omega
  simp [rvec, hk', not_lt.2 hk]

def phi (j : ℕ) (p : (SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) : Gn g (m + 1) :=
  cyc g (m + 1) * hpGL (rvec j p.2.1 p.2.2) (by rw [rvec_last]; exact p.2.1.ne_zero) * umGL p.1

theorem hp_um_row (r : Fin (m + 1) → ZMod g) (N : SIdx m → ZMod g) (i : Fin (m + 1)) (hi : i ≠ Fin.last m)
    (k : Fin (m + 1)) : (Hp r * Um N : Mt g (m + 1)) i k = Um N i k := by
  rw [Matrix.mul_apply]
  simp only [Hp, Matrix.of_apply, if_neg hi]
  rw [← Matrix.mul_apply, Matrix.one_mul]

theorem hp_um_last_low {j : ℕ} (r : Fin (m + 1) → ZMod g) (N : SIdx m → ZMod g)
    (hr : ∀ l : Fin (m + 1), (l : ℕ) ≤ j → r l = 0) (k : Fin (m + 1)) (hk : (k : ℕ) ≤ j) :
    (Hp r * Um N : Mt g (m + 1)) (Fin.last m) k = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  have hH : Hp r (Fin.last m) l = r l := by simp [Hp]
  rw [hH]
  by_cases hl : (l : ℕ) ≤ j
  · rw [hr l hl, zero_mul]
  · rw [um_upper N (show k < l by rw [Fin.lt_def]; omega), mul_zero]

theorem phi_val (j : ℕ) (p : (SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) :
    ((phi j p : Gn g (m + 1)) : Mt g (m + 1)) =
      ((cyc g (m + 1) : Gn g (m + 1)) : Mt g (m + 1)) * (Hp (rvec j p.2.1 p.2.2) * Um p.1) := by
  simp only [phi, Units.val_mul, hpGL_val, umGL_val, Matrix.mul_assoc]

theorem isY_phi {j : ℕ} (hj : j < m) (p : (SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) :
    IsY j ((phi j p : Gn g (m + 1)) : Mt g (m + 1)) := by
  rw [phi_val]
  constructor
  · intro i hi
    rw [cyc_mul_apply, rot_symm_zero]
    exact hp_um_last_low _ _ (fun l hl => rvec_low hj _ _ l hl) i hi
  · intro i k hik
    have hk : k ≠ 0 := by
      intro h
      subst h
      exact Fin.not_lt_zero i hik
    rw [cyc_mul_apply, hp_um_row _ _ _ (rot_symm_ne_last k hk)]
    have hv := rot_symm_val k hk
    have hik' : (i : ℕ) < k := hik
    simp only [Um, Matrix.of_apply]
    by_cases e : (k : ℕ) = i + 1
    · have : (finRotate (m + 1)).symm k = i := Fin.ext (by omega)
      rw [if_pos this, if_pos e]
    · have h1 : (finRotate (m + 1)).symm k ≠ i := fun h => e (by rw [← hv, h])
      have h2 : ¬ (finRotate (m + 1)).symm k < i := fun h => by
        have : (((finRotate (m + 1)).symm k : Fin (m + 1)) : ℕ) < i := h
        omega
      rw [if_neg h1, dif_neg h2, if_neg e]

end DiscreteGroups.sglob.DzFe
