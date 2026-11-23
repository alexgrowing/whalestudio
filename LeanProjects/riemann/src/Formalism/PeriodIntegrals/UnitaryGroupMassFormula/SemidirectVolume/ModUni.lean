import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModVec

noncomputable section

namespace PI.VolSemiDirect.W.PG

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

variable {D : Dat A n r}

theorem L_uni (H : D.Hyp) {w : Fin r → n → A} {s : Fin r → Fin r → A} (hw : ∀ a, IsW D (w a))
    (hs : ∀ a b, s a b + D.σA (s b a) + D.h (w a) (w b) = 0) : D.Uni (D.L w s) := by
  intro x y
  have hwp : ∀ a v, D.h (w a) (D.pW v) = D.h (w a) v := by
    intro a v
    conv_rhs => rw [show v = D.pU v + D.pW v by rw [pW_apply]; abel]
    rw [h_add_right, h_W_pU H (hw a), zero_add]
  have hL : ∀ v, D.L w s v = v + (∑ b, D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) -
      ∑ a, D.h (w a) v • D.e a) := by
    intro v
    rw [L_apply, add_sub_assoc]
    simp only [hwp]
  have k1 : ∀ u v, D.h u (∑ b, D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) -
      ∑ a, D.h (w a) v • D.e a) = ∑ b, D.h (D.e b) v * (D.h u (w b) + ∑ a, s a b * D.h u (D.e a)) -
      ∑ a, D.h (w a) v * D.h u (D.e a) := by
    intro u v
    simp only [h_sub_right, h_sum_right, h_smul_right, h_add_right]
  have k2 : ∀ v u, D.h (∑ b, D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) -
      ∑ a, D.h (w a) v • D.e a) u = ∑ b, D.σA (D.h (D.e b) v) * (D.h (w b) u +
      ∑ a, D.σA (s a b) * D.h (D.e a) u) - ∑ a, D.σA (D.h (w a) v) * D.h (D.e a) u := by
    intro v u
    simp only [h_sub_left, h_sum_left, h_smul_left, h_add_left]
  have zwe : ∀ b a, D.h (w b) (D.e a) = 0 := fun b a => h_W_e H (hw b) a
  have zew : ∀ a b, D.h (D.e a) (w b) = 0 := fun a b => (hw b).1 a
  have k3 : D.h (∑ b, D.h (D.e b) x • (w b + ∑ a, s a b • D.e a) - ∑ a, D.h (w a) x • D.e a)
      (∑ b, D.h (D.e b) y • (w b + ∑ a, s a b • D.e a) - ∑ a, D.h (w a) y • D.e a) =
      ∑ b, D.σA (D.h (D.e b) x) * ∑ d, D.h (D.e d) y * D.h (w b) (w d) := by
    rw [k2]
    simp only [k1, zwe, zew, H.ee, mul_zero, Finset.sum_const_zero, add_zero, sub_zero]
  have sxw : ∀ b, D.h x (w b) = D.σA (D.h (w b) x) := fun b => h_symm H (w b) x
  have sxe : ∀ a, D.h x (D.e a) = D.σA (D.h (D.e a) x) := fun a => h_symm H (D.e a) x
  have sww : ∀ a, D.σA (D.σA (D.h (w a) x)) = D.h (w a) x := fun a => H.σσ _
  rw [hL x, hL y, h_add_left, h_add_right, h_add_right, k1, k2, k3]
  simp only [sxw, sxe]

  have E1 : ∑ b, D.h (D.e b) y * (D.σA (D.h (w b) x) + ∑ a, s a b * D.σA (D.h (D.e a) x)) =
      ∑ b, D.h (D.e b) y * D.σA (D.h (w b) x) +
        ∑ b, ∑ a, D.h (D.e b) y * (s a b * D.σA (D.h (D.e a) x)) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have E2 : ∑ b, D.σA (D.h (D.e b) x) * (D.h (w b) y + ∑ a, D.σA (s a b) * D.h (D.e a) y) =
      ∑ b, D.σA (D.h (D.e b) x) * D.h (w b) y +
        ∑ b, ∑ a, D.σA (D.h (D.e b) x) * (D.σA (s a b) * D.h (D.e a) y) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [E1, E2]
  have tableDegreeTwoSixteen : ∑ b, D.h (D.e b) y * D.σA (D.h (w b) x) =
      ∑ a, D.σA (D.h (w a) x) * D.h (D.e a) y :=
    Finset.sum_congr rfl fun b _ => mul_comm _ _
  have A34 : ∑ a, D.h (w a) y * D.σA (D.h (D.e a) x) =
      ∑ b, D.σA (D.h (D.e b) x) * D.h (w b) y :=
    Finset.sum_congr rfl fun b _ => mul_comm _ _
  have A257 : ∑ b, ∑ a, D.h (D.e b) y * (s a b * D.σA (D.h (D.e a) x)) +
      ∑ b, ∑ a, D.σA (D.h (D.e b) x) * (D.σA (s a b) * D.h (D.e a) y) +
      ∑ b, D.σA (D.h (D.e b) x) * ∑ d, D.h (D.e d) y * D.h (w b) (w d) = 0 := by
    rw [Finset.sum_comm (f := fun b a => D.h (D.e b) y * (s a b * D.σA (D.h (D.e a) x)))]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    have := hs a b
    linear_combination (D.σA (D.h (D.e a) x) * D.h (D.e b) y) * this
  linear_combination tableDegreeTwoSixteen - A34 + A257

end Dat

end PI.VolSemiDirect.W.PG
