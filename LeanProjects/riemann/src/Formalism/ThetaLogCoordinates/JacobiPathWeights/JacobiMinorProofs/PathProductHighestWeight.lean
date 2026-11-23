import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementA
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementC
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ActFormContract

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace A1hw

theorem hom_int {σ R M : Type*} [CommRing R] [AddCommMonoid M] (w : σ → M) (z : ℤ) :
    IsWeightedHomogeneous w ((z : ℤ) : MvPolynomial σ R) 0 := by
  rw [← map_intCast (C : R →+* MvPolynomial σ R)]
  exact isWeightedHomogeneous_C w _

theorem wt_step {σ R : Type*} [CommRing R] {n : ℕ} (w : σ → ℤ) (up : Bool) (m : Fin n) (s : ℤ)
    (Kf : Form (MvPolynomial σ R) n) (Xv : Fin n → MvPolynomial σ R)
    (hK : ∀ J, IsWeightedHomogeneous w (Kf J) (if m ∈ J then s else 0))
    (hX : ∀ m', IsWeightedHomogeneous w (Xv m') (if m' = m then (if up then s else -s) else 0))
    (J : Finset (Fin n)) : IsWeightedHomogeneous w (stepF up Kf Xv J) (if m ∈ J then s else 0) := by
  unfold stepF
  cases up
  · simp only [Bool.false_eq_true, if_false] at hX ⊢
    unfold contrF
    refine IsWeightedHomogeneous.sum _ _ _ fun m' hm' => ?_
    have := ((hom_int (R := R) w (sg J m')).mul (hX m')).mul (hK (insert m' J))
    convert this using 1
    rw [Finset.mem_compl] at hm'
    by_cases h : m' = m
    · subst h; simp [hm']
    · have h2 : m ∈ insert m' J ↔ m ∈ J := by simp [Finset.mem_insert, Ne.symm h]
      simp [h, h2]
  · simp only [if_true] at hX ⊢
    unfold wedgeF
    refine IsWeightedHomogeneous.sum _ _ _ fun m' hm' => ?_
    have := ((hom_int (R := R) w (sg J m')).mul (hK (J.erase m'))).mul (hX m')
    convert this using 1
    by_cases h : m' = m
    · subst h; simp [hm']
    · have h2 : m ∈ J.erase m' ↔ m ∈ J := by simp [Finset.mem_erase, Ne.symm h]
      simp [h, h2]

theorem sum_wt (x : ℤ) (S : Finset ℤ) (hS : Finset.Ioc 0 x ∪ Finset.Ioc x 0 ⊆ S) :
    ∑ c ∈ S, (if 1 ≤ c then (if c ≤ x then (1 : ℤ) else 0) else (if x < c then -1 else 0)) = x := by
  rw [← Finset.sum_subset hS]
  · rcases le_total 0 x with h | h
    · rw [Finset.Ioc_eq_empty (not_lt.2 h), Finset.union_empty]
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ))]
      · simp [h]
      · intro c hc
        rw [Finset.mem_Ioc] at hc
        rw [if_pos (by omega), if_pos hc.2]
    · rw [Finset.Ioc_eq_empty (not_lt.2 h), Finset.empty_union]
      rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℤ))]
      · simp [h]
      · intro c hc
        rw [Finset.mem_Ioc] at hc
        rw [if_neg (by omega), if_pos hc.1]
  · intro c _ hc
    rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ioc] at hc
    split_ifs <;> first | rfl | (exfalso; omega)

theorem mem_can {n : ℕ} {μN : Fin n → ℤ} (h : Antitone μN) (c : ℤ) (m : Fin n) :
    m ∈ canIdx μN c ↔ if 1 ≤ c then c ≤ μN m else μN m < c := by
  unfold canIdx
  split_ifs with hc
  · simp only [mem_filter, mem_univ, true_and]
    exact (Paths.le_iff_lt_colHeight h c m).symm
  · simp only [mem_filter, mem_univ, true_and]
    rw [← not_le, Paths.le_iff_lt_colHeight h c m, not_lt]

theorem isIndex_can {n : ℕ} (μN : Fin n → ℤ) : IsIndex μN (canIdx μN) := by
  intro c
  have hn := Paths.colHeight_le μN c
  unfold canIdx
  split_ifs with hc
  · have : (univ.filter fun m : Fin n => m.val < colHeight μN c) =
        (Finset.range (colHeight μN c)).attachFin (fun i hi => by
          rw [Finset.mem_range] at hi; omega) := by
      ext m; simp
    rw [this, Finset.card_attachFin, Finset.card_range]
  · have h1 : (univ.filter fun m : Fin n => colHeight μN c ≤ m.val) =
        (univ.filter fun m : Fin n => m.val < colHeight μN c)ᶜ := by
      ext m; simp
    have h2 : (univ.filter fun m : Fin n => m.val < colHeight μN c) =
        (Finset.range (colHeight μN c)).attachFin (fun i hi => by
          rw [Finset.mem_range] at hi; omega) := by
      ext m; simp
    rw [h1, Finset.card_compl, h2, Finset.card_attachFin, Finset.card_range, Fintype.card_fin]

theorem map_step {A A' : Type*} [CommRing A] [CommRing A'] (φ : A →+* A') {n : ℕ} (up : Bool)
    (K : Form A n) (K' : Form A' n) (Xv : Fin n → A) (hK : ∀ J, φ (K J) = K' J) (J : Finset (Fin n)) :
    φ (stepF up K Xv J) = stepF up K' (fun a => φ (Xv a)) J := by
  unfold stepF
  cases up
  · simp only [Bool.false_eq_true, if_false, contrF, map_sum, map_mul, map_intCast, hK]
  · simp only [if_true, wedgeF, map_sum, map_mul, map_intCast, hK]

theorem map_pathWord {A A' : Type*} [CommRing A] [CommRing A'] (φ : A →+* A') {n : ℕ}
    (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ) (Xr : ℕ → Fin n → A) :
    ∀ (j : ℕ) (J : Finset (Fin n)),
      φ (pathWord isVec μ c Xr j J) = pathWord isVec μ c (fun i a => φ (Xr i a)) j J := by
  intro j
  induction j with
  | zero =>
    intro J
    show φ (if J = ∅ then 1 else 0) = if J = ∅ then 1 else 0
    split <;> simp
  | succ j ih =>
    intro J
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, pathWord, if_pos hch, if_pos hch]
      exact ih J
    · rw [pathWord, pathWord, if_neg hch, if_neg hch]
      exact map_step φ _ _ _ _ ih J

theorem act_pathWord (hw : FactX2wedge) (hc : FactX2contr) {A : Type} [CommRing A] {n : ℕ}
    (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ) (Xc Xe : ℕ → Fin n → A)
    (g : (Matrix (Fin n) (Fin n) A)ˣ)
    (h1 : ∀ i, (isVec i == decide (1 ≤ c)) = true → Xe i = Matrix.vecMul (Xc i) (↑g : Matrix _ _ A))
    (h2 : ∀ i, (isVec i == decide (1 ≤ c)) = false →
      Xe i = Matrix.vecMul (Xc i) (↑g⁻¹ : Matrix _ _ A).transpose) :
    ∀ j : ℕ, pathWord isVec μ c Xe j = actF (pathWord isVec μ c Xc j) (↑g : Matrix _ _ A) := by
  intro j
  induction j with
  | zero => exact (actF_oneF _).symm
  | succ j ih =>
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, pathWord, if_pos hch, if_pos hch]
      exact ih
    · rw [pathWord, pathWord, if_neg hch, if_neg hch, ih]
      unfold stepF
      cases hup : (isVec j == decide (1 ≤ c))
      · simp only [Bool.false_eq_true, if_false]
        rw [hc, h2 j hup]
      · simp only [if_true]
        rw [hw, h1 j hup]

def tv {A : Type*} [CommRing A] {n : ℕ} (a b : Fin n) (hab : a ≠ b) (t : A) :
    (Matrix (Fin n) (Fin n) A)ˣ where
  val := Matrix.transvection a b t
  inv := Matrix.transvection a b (-t)
  val_inv := by rw [Matrix.transvection_mul_transvection_same _ _ hab]; simp
  inv_val := by rw [Matrix.transvection_mul_transvection_same _ _ hab]; simp

theorem tv_apply {A : Type*} [CommRing A] {n : ℕ} (a b : Fin n) (t : A) (i j : Fin n) :
    Matrix.transvection a b t i j = (if i = j then 1 else 0) + if a = i ∧ b = j then t else 0 := by
  simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

end A1hw

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
