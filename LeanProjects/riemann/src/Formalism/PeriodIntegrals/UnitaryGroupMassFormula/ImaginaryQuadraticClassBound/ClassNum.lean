import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ImaginaryQuadraticClassBound.Development

open NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace PI.RayBoundIQW

section Lattice

variable {R : Type*} [CommRing R]

def HData (I : Ideal R) (e1 e2 : R) (a c b : ℕ) : Prop :=
  0 < a ∧ 0 < c ∧ b < a ∧ ((a : ℤ) : R) * e1 ∈ I ∧ ((b : ℤ) : R) * e1 + ((c : ℤ) : R) * e2 ∈ I ∧
    (∀ n : ℕ, 0 < n → n < a → ((n : ℤ) : R) * e1 ∉ I) ∧
    (∀ n : ℕ, 0 < n → n < c → ∀ x : ℤ, (x : R) * e1 + ((n : ℤ) : R) * e2 ∉ I)

theorem HData.minA {I : Ideal R} {e1 e2 : R} {a c b : ℕ} (hP : HData I e1 e2 a c b)
    (x : ℤ) (hx : (x : R) * e1 ∈ I) (h1 : -(a : ℤ) < x) (h2 : x < a) : x = 0 := by
  obtain ⟨-, -, -, -, -, hamin, -⟩ := hP
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine hamin (-x).toNat (by omega) (by omega) ?_
    have e : ((((-x).toNat : ℕ) : ℤ) : R) = -(x : R) := by
      rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [e]
    convert I.neg_mem hx using 1; ring
  · refine hamin x.toNat (by omega) (by omega) ?_
    rwa [Int.toNat_of_nonneg hpos.le]

theorem HData.minC {I : Ideal R} {e1 e2 : R} {a c b : ℕ} (hP : HData I e1 e2 a c b)
    (x y : ℤ) (hx : (x : R) * e1 + (y : R) * e2 ∈ I) (h1 : -(c : ℤ) < y) (h2 : y < c) :
    y = 0 := by
  obtain ⟨-, -, -, -, -, -, hcmin⟩ := hP
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine hcmin (-y).toNat (by omega) (by omega) (-x) ?_
    have e : ((((-y).toNat : ℕ) : ℤ) : R) = -(y : R) := by
      rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [e]
    convert I.neg_mem hx using 1; push_cast; ring
  · refine hcmin y.toNat (by omega) (by omega) x ?_
    rwa [Int.toNat_of_nonneg hpos.le]

theorem HData.le {I J : Ideal R} {e1 e2 : R} {a c b : ℕ}
    (hspan : ∀ z : R, ∃ x y : ℤ, z = (x : R) * e1 + (y : R) * e2)
    (hP : HData I e1 e2 a c b) (haJ : ((a : ℤ) : R) * e1 ∈ J)
    (hbJ : ((b : ℤ) : R) * e1 + ((c : ℤ) : R) * e2 ∈ J) : I ≤ J := by
  intro z hz
  obtain ⟨x, y, rfl⟩ := hspan z
  have hc0 : (0 : ℤ) < c := by exact_mod_cast hP.2.1
  have ha0 : (0 : ℤ) < a := by exact_mod_cast hP.1
  obtain ⟨q, r, hr0, hrc, rfl⟩ : ∃ q r : ℤ, 0 ≤ r ∧ r < c ∧ y = c * q + r :=
    ⟨y / c, y % c, Int.emod_nonneg _ hc0.ne', Int.emod_lt_of_pos _ hc0,
      (Int.mul_ediv_add_emod y c).symm⟩
  have hz1 : ((x - q * b : ℤ) : R) * e1 + (r : R) * e2 ∈ I := by
    have := I.sub_mem hz (I.mul_mem_left (q : R) hP.2.2.2.2.1)
    convert this using 1; push_cast; ring
  have hr : r = 0 := hP.minC _ _ hz1 (by omega) hrc
  subst hr
  obtain ⟨q', t, ht0, hta, hs⟩ : ∃ q' t : ℤ, 0 ≤ t ∧ t < a ∧ x - q * b = a * q' + t :=
    ⟨(x - q * b) / a, (x - q * b) % a, Int.emod_nonneg _ ha0.ne', Int.emod_lt_of_pos _ ha0,
      (Int.mul_ediv_add_emod _ _).symm⟩
  have hz2 : (t : R) * e1 ∈ I := by
    have := I.sub_mem hz1 (I.mul_mem_left (q' : R) hP.2.2.2.1)
    convert this using 1; rw [hs]; push_cast; ring
  have ht : t = 0 := hP.minA _ hz2 (by omega) hta
  subst ht
  have hx : x = a * q' + q * b := by linarith
  subst hx
  have := J.add_mem (J.mul_mem_left (q' : R) haJ) (J.mul_mem_left (q : R) hbJ)
  convert this using 1; push_cast; ring

end Lattice

end PI.RayBoundIQW
