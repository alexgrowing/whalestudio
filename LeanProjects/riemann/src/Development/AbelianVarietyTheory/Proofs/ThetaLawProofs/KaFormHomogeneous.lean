import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.AlternatingSumChooseMulSubPow

namespace GlobalTheory

open Finset GlobalTheory.KeyKa

private theorem kaForm_prod_zpow {G : Type} [CommGroup G] (a : G) (s : Finset ℕ) (f : ℕ → ℤ) :
    ∏ j ∈ s, a ^ f j = a ^ ∑ j ∈ s, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [prod_insert hj, sum_insert hj, ih, zpow_add]

theorem tComb_rescale {R : Type} [CommRing R] (g n l Pr : ℕ) (t a : Rˣ) (lam be : ℕ → Rˣ)
    (hl : g * n < l) (hd : ∀ j ∈ range (g + 1), (l - j * n) ∣ Pr) :
    tComb g n l Pr (t * ∏ j ∈ range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ)))
      (fun j => lam j * be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ) *
        a ^ (8 * (l - j * n) ^ (4 * g + 2)))
      = tComb g n l Pr t lam *
        a ^ (8 * ((Pr ^ (3 * g + 2) : ℕ) : ℤ) * ((g.factorial * n ^ g : ℕ) : ℤ)) := by
  unfold tComb
  rw [mul_pow]
  simp only [mul_zpow, prod_mul_distrib]
  have hB : (∏ j ∈ range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) ^ (4 * Pr ^ (3 * g + 2)) *
      ∏ j ∈ range (g + 1), (be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ)) ^
        ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ)) = 1 := by
    rw [← prod_pow, ← prod_mul_distrib]
    refine prod_eq_one fun j hj => ?_
    rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    convert zpow_zero (be j) using 2
    have key : Pr / (l - j * n) * (l - j * n) = Pr := Nat.div_mul_cancel (hd j hj)
    generalize Pr / (l - j * n) = q at key ⊢
    generalize l - j * n = d at key ⊢
    subst key
    push_cast
    ring
  have hA : ∏ j ∈ range (g + 1), (a ^ (8 * (l - j * n) ^ (4 * g + 2))) ^
        ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ)) =
      a ^ (8 * ((Pr ^ (3 * g + 2) : ℕ) : ℤ) * ((g.factorial * n ^ g : ℕ) : ℤ)) := by
    rw [prod_congr rfl fun j _ => by rw [← zpow_natCast, ← zpow_mul], kaForm_prod_zpow,
      ← alternating_sum_choose_mul_sub_pow g n l hl.le, mul_sum]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    have key : Pr / (l - j * n) * (l - j * n) = Pr := Nat.div_mul_cancel (hd j hj)
    generalize Pr / (l - j * n) = q at key ⊢
    generalize l - j * n = d at key ⊢
    subst key
    push_cast
    ring
  calc _ = t ^ (4 * Pr ^ (3 * g + 2)) *
        (∏ j ∈ range (g + 1), lam j ^ ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ))) *
        ((∏ j ∈ range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) ^ (4 * Pr ^ (3 * g + 2)) *
          ∏ j ∈ range (g + 1), (be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ)) ^
            ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ))) *
        ∏ j ∈ range (g + 1), (a ^ (8 * (l - j * n) ^ (4 * g + 2))) ^
          ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ)) := by ac_rfl
    _ = _ := by rw [hB, hA, mul_one]

theorem tComb_mul_left {R : Type} [CommRing R] (g n l Pr : ℕ) (t c : Rˣ) (lam : ℕ → Rˣ) :
    tComb g n l Pr (t * c) lam = tComb g n l Pr t lam * c ^ (4 * Pr ^ (3 * g + 2)) := by
  unfold tComb
  rw [mul_pow]
  exact mul_right_comm _ _ _

private theorem kaForm_monomial_eq_of_exponent_relations {G : Type} [CommGroup G] (X X' J u dl a : G) (N k : ℕ)
    (z1 z2 z3 α e1 e2 e3 : ℤ) (hu : z1 * N * e1 + z2 * N * e2 + z3 * e3 = 0)
    (hdl : 2 * N * e1 + 2 * N * e2 + 2 * e3 = 0) (ha : α * e1 + α * e2 + k = 0) :
    (X * (u ^ z1) ^ N * (dl ^ 2) ^ N * a ^ α) ^ e1 * (X' * (u ^ z2) ^ N * (dl ^ 2) ^ N * a ^ α) ^ e2 *
      (J * u ^ z3 * dl ^ 2) ^ e3 * a ^ k = X ^ e1 * X' ^ e2 * J ^ e3 := by
  have eU : u ^ (z1 * N * e1) * u ^ (z2 * N * e2) * u ^ (z3 * e3) = 1 := by
    rw [← zpow_add, ← zpow_add, hu, zpow_zero]
  have eD : dl ^ (2 * N * e1) * dl ^ (2 * N * e2) * dl ^ (2 * e3) = 1 := by
    rw [← zpow_add, ← zpow_add, hdl, zpow_zero]
  have eA : a ^ (α * e1) * a ^ (α * e2) * a ^ (k : ℤ) = 1 := by
    rw [← zpow_add, ← zpow_add, ha, zpow_zero]
  simp only [mul_zpow, ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat]
  calc _ = X ^ e1 * X' ^ e2 * J ^ e3 * (u ^ (z1 * N * e1) * u ^ (z2 * N * e2) * u ^ (z3 * e3)) *
        (dl ^ (2 * N * e1) * dl ^ (2 * N * e2) * dl ^ (2 * e3)) *
        (a ^ (α * e1) * a ^ (α * e2) * a ^ (k : ℤ)) := by simp only [mul_comm, mul_assoc, mul_left_comm]
    _ = _ := by rw [eU, eD, eA, mul_one, mul_one, mul_one]

theorem kaForm_homogeneous :
    ∀ (R : Type) [CommRing R] (g n l l' : ℕ) (t t' J u a dl : Rˣ) (lam lam' be be' : ℕ → Rˣ), g * n < l → l < l' → kaForm g n l l' (t * u ^ (-2 * (l : ℤ)) * dl ^ 2 * ∏ j ∈ Finset.range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) (t' * u ^ (-2 * (l' : ℤ)) * dl ^ 2 * ∏ j ∈ Finset.range (g + 1), be' j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) (fun j => lam j * be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ) * a ^ (8 * (l - j * n) ^ (4 * g + 2))) (fun j => lam' j * be' j ^ (-8 * ((l' - j * n) ^ (3 * g + 2) : ℕ) : ℤ) * a ^ (8 * (l' - j * n) ^ (4 * g + 2))) (J * u ^ (-((g * n : ℕ) : ℤ)) * dl ^ 2) * a ^ (8 * kaExp g n l l') = kaForm g n l l' t t' lam lam' J := by
  intro R _ g n l l' t t' J u a dl lam lam' be be' hl hl'
  have hd : ∀ j ∈ range (g + 1), (l - j * n) ∣ degProd g n l l' := fun j hj =>
    (dvd_mul_right _ _).trans (dvd_prod_of_mem (fun j => (l - j * n) * (l' - j * n)) hj)
  have hd' : ∀ j ∈ range (g + 1), (l' - j * n) ∣ degProd g n l l' := fun j hj =>
    (dvd_mul_left _ _).trans (dvd_prod_of_mem (fun j => (l - j * n) * (l' - j * n)) hj)
  unfold kaForm
  rw [tComb_rescale g n l _ _ a lam be hl hd, tComb_rescale g n l' _ _ a lam' be' (hl.trans hl') hd',
    tComb_mul_left, tComb_mul_left, tComb_mul_left, tComb_mul_left]
  refine kaForm_monomial_eq_of_exponent_relations _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
  all_goals
    try unfold kaExp
    push_cast [Nat.cast_sub hl'.le]
    ring

end GlobalTheory
