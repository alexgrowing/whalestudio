import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularOrthogonal.MatOrthoLocal

noncomputable section

namespace PI.UnimodularOrthogonalQuadratic.Loc

open Matrix

section Star

variable {S : Type} [CommRing S] [StarRing S]

structure LocHyp (S : Type) [CommRing S] [StarRing S] : Prop where
  two : IsUnit (2 : S)
  add : ∀ x y : S, star x = x → star y = y → ¬IsUnit x → ¬IsUnit y → ¬IsUnit (x + y)
  norm : ∀ x : S, star x = x → IsUnit x → ∃ u, u * star u = x

def q {n : ℕ} (H : Matrix (Fin n) (Fin n) S) (v : Fin n → S) : S :=
  ∑ l, (∑ k, v k * H k l) * star (v l)

theorem q_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) S) (u : S) (v : Fin n → S) :
    q H (u • v) = u * star u * q H v := by
  simp only [q, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem star_eq_of_herm {n : ℕ} {H : Matrix (Fin n) (Fin n) S} (hH : Hᴴ = H) (k l : Fin n) :
    star (H k l) = H l k := by
  rw [← conjTranspose_apply, hH]

theorem q_fixed {n : ℕ} {H : Matrix (Fin n) (Fin n) S} (hH : Hᴴ = H) (v : Fin n → S) :
    star (q H v) = q H v := by
  simp only [q, star_sum, star_mul', star_star, star_eq_of_herm hH, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem cong_apply_self {n : ℕ} (P H : Matrix (Fin n) (Fin n) S) (a : Fin n) :
    (P * H * Pᴴ) a a = q H (P a) := by
  simp only [mul_apply, q, conjTranspose_apply]

theorem herm_cong {n : ℕ} (P : Matrix (Fin n) (Fin n) S) {H : Matrix (Fin n) (Fin n) S} (hH : Hᴴ = H) :
    (P * H * Pᴴ)ᴴ = P * H * Pᴴ := by
  simp [conjTranspose_mul, hH, Matrix.mul_assoc]

theorem det_cong {n : ℕ} {P H : Matrix (Fin n) (Fin n) S} (hP : IsUnit P.det) (hH : IsUnit H.det) :
    IsUnit (P * H * Pᴴ).det := by
  rw [det_mul, det_mul, det_conjTranspose]
  exact (hP.mul hH).mul hP.star

theorem det_updateRow_zero {n : ℕ} (w : Fin (n + 1) → S) :
    (updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) S) 0 w).det = w 0 := by
  have hup : (updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) S) 0 w).IsUpperTriangular := by
    intro i j hij
    have hi : i ≠ 0 := by
      rintro rfl
      exact Fin.not_lt_zero _ hij
    rw [updateRow_ne hi]
    exact one_apply_ne (ne_of_lt hij).symm
  rw [det_of_isUpperTriangular hup, Fin.prod_univ_succ]
  simp [updateRow_ne (Fin.succ_ne_zero _)]

def elim {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) S) : Matrix (Fin (n + 1)) (Fin (n + 1)) S :=
  Matrix.of (Fin.cons (Pi.single 0 1 : Fin (n + 1) → S)
    fun i : Fin n => (Fin.cons (-A i.succ 0) (Pi.single i 1 : Fin n → S) : Fin (n + 1) → S))

theorem det_elim {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) S) : (elim A).det = 1 := by
  have hlow : (elim A).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · have hj : j ≠ 0 := (ne_of_lt hij').symm
      simp [elim, Pi.single_apply, hj]
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · exact absurd hij' (Fin.not_lt_zero _)
      · have : j ≠ i := (ne_of_lt (Fin.succ_lt_succ_iff.mp hij')).symm
        simp [elim, Pi.single_apply, this]
  rw [det_of_isLowerTriangular _ hlow, Fin.prod_univ_succ]
  simp [elim]

theorem elimination_mul_first_row {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (b : Fin (n + 1)) :
    (elim A * A) 0 b = A 0 b := by
  simp [elim, mul_apply, Pi.single_apply]

theorem elim_mul_col {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) S} (h : A 0 0 = 1) (a : Fin (n + 1)) :
    (elim A * A) a 0 = if a = 0 then 1 else 0 := by
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
  · simp [elimination_mul_first_row, h]
  · simp [elim, mul_apply, Fin.sum_univ_succ, h, Pi.single_apply, Fin.succ_ne_zero]

theorem row0 {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) S} (hA : Aᴴ = A) (h : A 0 0 = 1) (b : Fin (n + 1)) :
    (elim A * A * (elim A)ᴴ) 0 b = if b = 0 then 1 else 0 := by
  have e1 : (elim A * A * (elim A)ᴴ) 0 b = (A * (elim A)ᴴ) 0 b := by
    rw [mul_apply (M := elim A * A), mul_apply (M := A)]
    exact Finset.sum_congr rfl fun l _ => by rw [elimination_mul_first_row]
  rw [e1, show A * (elim A)ᴴ = (elim A * A)ᴴ by rw [conjTranspose_mul, hA], conjTranspose_apply,
    elim_mul_col h]
  split_ifs <;> simp

theorem det_of_first_row_single {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (h : ∀ b, M 0 b = if b = 0 then 1 else 0) :
    M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  simp [h, Fin.succ_ne_zero]

def blk {n : ℕ} (P : Matrix (Fin n) (Fin n) S) : Matrix (Fin (n + 1)) (Fin (n + 1)) S :=
  Matrix.of (Fin.cons (Pi.single 0 1 : Fin (n + 1) → S)
    fun i : Fin n => (Fin.cons (0 : S) (P i) : Fin (n + 1) → S))

theorem det_blk {n : ℕ} (P : Matrix (Fin n) (Fin n) S) : (blk P).det = P.det := by
  rw [det_of_first_row_single _ (fun b => by simp [blk, Pi.single_apply])]
  congr 1

theorem blk_cong {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) S} {P : Matrix (Fin n) (Fin n) S}
    (hrow : ∀ b, M 0 b = if b = 0 then 1 else 0) (hcol : ∀ a, M a 0 = if a = 0 then 1 else 0)
    (hP : P * M.submatrix Fin.succ Fin.succ * Pᴴ = 1) : blk P * M * (blk P)ᴴ = 1 := by
  have hr0 : M 0 0 = 1 := by simp [hrow]
  have hrs : ∀ j : Fin n, M 0 j.succ = 0 := fun j => by simp [hrow, Fin.succ_ne_zero]
  have hcs : ∀ i : Fin n, M i.succ 0 = 0 := fun i => by simp [hcol, Fin.succ_ne_zero]
  ext a b
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
  · simp [blk, mul_apply, Fin.sum_univ_succ, hr0, hrs, hcs, one_apply]
  · simp [blk, mul_apply, Fin.sum_univ_succ, hr0, hrs, hcs, one_apply, (Fin.succ_ne_zero j).symm]
  · simp [blk, mul_apply, Fin.sum_univ_succ, hr0, hrs, hcs, one_apply]
  · have := congrFun (congrFun hP i) j
    simp only [mul_apply, submatrix_apply, conjTranspose_apply] at this
    simp [blk, mul_apply, Fin.sum_univ_succ, hr0, hrs, hcs, one_apply] at this ⊢
    exact this

theorem step (hL : LocHyp S) {n : ℕ}
    (IH : ∀ H : Matrix (Fin n) (Fin n) S, Hᴴ = H → IsUnit H.det →
      ∃ P : Matrix (Fin n) (Fin n) S, IsUnit P.det ∧ P * H * Pᴴ = 1)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) S} (hH : Hᴴ = H) (hdet : IsUnit H.det)
    {v : Fin (n + 1) → S} (hv : v 0 = 1) (hq : IsUnit (q H v)) :
    ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) S, IsUnit P.det ∧ P * H * Pᴴ = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, w * q H v = 1 := ⟨_, hq.val_inv_mul⟩
  have hqs : star (q H v) = q H v := q_fixed hH v
  have hws : star w = w := by
    have h1 : star w * q H v = 1 := by rw [← hqs, ← star_mul', hw, star_one]
    linear_combination w * h1 - (star w) * hw
  obtain ⟨u, hu⟩ := hL.norm w hws (isUnit_iff_exists_inv.mpr ⟨_, hw⟩)
  have huq : u * star u * q H v = 1 := by rw [hu, hw]
  have hu1 : IsUnit u := isUnit_iff_exists_inv.mpr ⟨star u * q H v, by rw [← mul_assoc, huq]⟩
  set P1 : Matrix (Fin (n + 1)) (Fin (n + 1)) S := updateRow 1 0 (u • v) with hP1
  have hP1d : IsUnit P1.det := by
    rw [hP1, det_updateRow_zero]
    simpa [hv] using hu1
  set H1 := P1 * H * P1ᴴ with hH1def
  have hH1 : H1ᴴ = H1 := herm_cong P1 hH
  have hH1d : IsUnit H1.det := det_cong hP1d hdet
  have hH100 : H1 0 0 = 1 := by
    rw [hH1def, cong_apply_self, hP1, updateRow_self, q_smul, huq]
  have hEd : IsUnit (elim H1).det := by rw [det_elim]; exact isUnit_one
  set H2 := elim H1 * H1 * (elim H1)ᴴ with hH2def
  have hH2 : H2ᴴ = H2 := herm_cong _ hH1
  have hH2d : IsUnit H2.det := det_cong hEd hH1d
  have hrow : ∀ b, H2 0 b = if b = 0 then 1 else 0 := row0 hH1 hH100
  have hcol : ∀ a, H2 a 0 = if a = 0 then 1 else 0 := fun a => by
    rw [← star_eq_of_herm hH2 0 a, hrow]
    split_ifs <;> simp
  have hH3 : (H2.submatrix Fin.succ Fin.succ)ᴴ = H2.submatrix Fin.succ Fin.succ := by
    rw [conjTranspose_submatrix, hH2]
  have hH3d : IsUnit (H2.submatrix Fin.succ Fin.succ).det := by
    rw [← det_of_first_row_single H2 hrow]
    exact hH2d
  obtain ⟨P3, hP3d, hP3⟩ := IH _ hH3 hH3d
  refine ⟨blk P3 * elim H1 * P1, ?_, ?_⟩
  · rw [det_mul, det_mul, det_blk]
    exact (hP3d.mul hEd).mul hP1d
  · have : blk P3 * elim H1 * P1 * H * (blk P3 * elim H1 * P1)ᴴ = blk P3 * H2 * (blk P3)ᴴ := by
      simp only [hH2def, hH1def, conjTranspose_mul, Matrix.mul_assoc]
    rw [this]
    exact blk_cong hrow hcol hP3

end Star

end PI.UnimodularOrthogonalQuadratic.Loc

namespace PI.UnimodularOrthogonalQuadratic

open Matrix

end PI.UnimodularOrthogonalQuadratic
