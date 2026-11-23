import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory

open GradedHilbert

section

variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι)

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma decompose_X_smul_add_one (y : M) (m : ℤ) :
    (decompose ℳ ((X i : MvPolynomial ι R) • y) (m + 1) : M) =
      (X i : MvPolynomial ι R) • (decompose ℳ y m : M) := by
  classical
  have key : ∀ j, (decompose ℳ ((X i : MvPolynomial ι R) • (decompose ℳ y j : M)) (m + 1) : M)
      = if j = m then (X i : MvPolynomial ι R) • (decompose ℳ y m : M) else 0 := by
    intro j
    have hmem := _root_.GlobalTheory.X_smul_mem_gr ℳ i j _ (decompose ℳ y j).2
    split_ifs with hj
    · subst hj; exact decompose_of_mem_same ℳ hmem
    · exact decompose_of_mem_ne ℳ hmem (by omega)
  conv_lhs => rw [← sum_support_decompose ℳ y]
  rw [Finset.smul_sum, decompose_sum, DFinsupp.finset_sum_apply, Submodule.coe_sum]
  simp only [key]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [DFinsupp.notMem_support_iff.1 h]; simp

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma decompose_X_sub_one_smul_add_one (w : M) (m : ℤ) :
    (decompose ℳ ((X i - 1 : MvPolynomial ι R) • w) (m + 1) : M) =
      (X i : MvPolynomial ι R) • (decompose ℳ w m : M) - (decompose ℳ w (m + 1) : M) := by
  rw [sub_smul, one_smul, decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
    decompose_X_smul_add_one]

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma exists_decompose_eq_zero_of_lt (y : M) :
    ∃ N : ℤ, ∀ j < N, (decompose ℳ y j : M) = 0 := by
  classical
  obtain ⟨N, hN⟩ := (decompose ℳ y).support.bddBelow
  refine ⟨N, fun j hj => ?_⟩
  have : j ∉ (decompose ℳ y).support := fun h => by have := hN h; omega
  simp [DFinsupp.notMem_support_iff.1 this]

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma exists_decompose_eq_zero_of_gt (y : M) :
    ∃ N : ℤ, ∀ j > N, (decompose ℳ y j : M) = 0 := by
  classical
  obtain ⟨N, hN⟩ := (decompose ℳ y).support.bddAbove
  refine ⟨N, fun j hj => ?_⟩
  have : j ∉ (decompose ℳ y).support := fun h => by have := hN h; omega
  simp [DFinsupp.notMem_support_iff.1 this]

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma eq_zero_of_X_smul_recurrence_of_vanish_below {g : ℤ → M} {N c : ℤ} (hN : ∀ j < N, g j = 0)
    (hrec : ∀ m < c, g (m + 1) = (X i : MvPolynomial ι R) • g m) : g c = 0 := by
  have key : ∀ k : ℕ, g c = (X i : MvPolynomial ι R) ^ k • g (c - k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : c - (k : ℤ) = c - ((k + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [ih, e, hrec _ (by omega), ← mul_smul, ← pow_succ]
  rw [key (c - N + 1).toNat, hN _ (by omega), smul_zero]

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma exists_X_pow_smul_eq_zero_of_vanish_above {g : ℤ → M} {N c : ℤ}
    (hN : ∀ j > N, g j = 0) (hrec : ∀ m ≥ c, g (m + 1) = (X i : MvPolynomial ι R) • g m) :
    ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • g c = 0 := by
  have key : ∀ k : ℕ, g (c + k) = (X i : MvPolynomial ι R) ^ k • g c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc, hrec _ (by omega), ih, ← mul_smul, ← pow_succ']
  exact ⟨(N - c + 1).toNat, by rw [← key, hN _ (by omega)]⟩

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in

theorem _root_.GlobalTheory.exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul {n : ℤ} {z w : M} (hz : z ∈ ℳ n)
    (h : z = (X i - 1 : MvPolynomial ι R) • w) :
    ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z = 0 := by
  have hcomp : ∀ m, (decompose ℳ z (m + 1) : M) =
      (X i : MvPolynomial ι R) • (decompose ℳ w m : M) - (decompose ℳ w (m + 1) : M) := by
    intro m; rw [h]; exact decompose_X_sub_one_smul_add_one ℳ i w m
  have hne : ∀ m, m + 1 ≠ n →
      (decompose ℳ w (m + 1) : M) = (X i : MvPolynomial ι R) • (decompose ℳ w m : M) := by
    intro m hm
    have := hcomp m
    rw [decompose_of_mem_ne ℳ hz (Ne.symm hm)] at this
    exact (sub_eq_zero.1 this.symm).symm
  obtain ⟨N₁, hN₁⟩ := exists_decompose_eq_zero_of_lt ℳ w
  obtain ⟨N₂, hN₂⟩ := exists_decompose_eq_zero_of_gt ℳ w
  have h1 : (decompose ℳ w (n - 1) : M) = 0 :=
    eq_zero_of_X_smul_recurrence_of_vanish_below i (g := fun m => (decompose ℳ w m : M)) hN₁
      (fun m hm => hne m (by omega))
  have hzn : z = -(decompose ℳ w n : M) := by
    have := hcomp (n - 1)
    rw [sub_add_cancel, decompose_of_mem_same ℳ hz, h1, smul_zero, zero_sub] at this
    exact this
  obtain ⟨k, hk⟩ := exists_X_pow_smul_eq_zero_of_vanish_above i
    (g := fun m => (decompose ℳ w m : M)) (c := n) hN₂ (fun m hm => hne m (by omega))
  exact ⟨k, by rw [hzn, smul_neg, hk, neg_zero]⟩

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma X_pow_smul_mem_add_of_mem {j : ℤ} {v : M} (hv : v ∈ ℳ j) (k : ℕ) :
    (X i : MvPolynomial ι R) ^ k • v ∈ ℳ (j + k) := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have := _root_.GlobalTheory.X_smul_mem_gr ℳ i (j + k) _ ih
    rw [pow_succ', mul_smul]
    convert this using 2
    push_cast; ring

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma exists_mem_add_X_sub_one_smul_of_mem_of_le {j n : ℤ} {v : M} (hv : v ∈ ℳ j) (hn : j ≤ n) :
    ∃ y' ∈ ℳ n, ∃ w : M, v = y' + (X i - 1 : MvPolynomial ι R) • w := by
  have hmem := X_pow_smul_mem_add_of_mem ℳ i hv (n - j).toNat
  have e : j + ((n - j).toNat : ℤ) = n := by omega
  rw [e] at hmem
  refine ⟨_, hmem, -(∑ l ∈ Finset.range (n - j).toNat, (X i : MvPolynomial ι R) ^ l) • v, ?_⟩
  rw [neg_smul, smul_neg, smul_smul, mul_geom_sum, sub_smul, one_smul]
  abel

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in

theorem _root_.GlobalTheory.exists_homogeneous_add_X_sub_one_smul (y : M) :
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∃ y' ∈ ℳ n, ∃ w : M, y = y' + (X i - 1 : MvPolynomial ι R) • w := by
  classical
  have hsum : ∀ S : Finset ℤ, ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∃ y' ∈ ℳ n, ∃ w : M,
      ∑ j ∈ S, (decompose ℳ y j : M) = y' + (X i - 1 : MvPolynomial ι R) • w := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨0, fun n _ => ⟨0, zero_mem _, 0, by simp⟩⟩
    | insert a S ha ih =>
      obtain ⟨n₁, hn₁⟩ := ih
      refine ⟨max a n₁, fun n hn => ?_⟩
      obtain ⟨y₁, hy₁, w₁, e₁⟩ :=
        exists_mem_add_X_sub_one_smul_of_mem_of_le ℳ i (decompose ℳ y a).2 (le_of_max_le_left hn)
      obtain ⟨y₂, hy₂, w₂, e₂⟩ := hn₁ n (le_of_max_le_right hn)
      refine ⟨y₁ + y₂, add_mem hy₁ hy₂, w₁ + w₂, ?_⟩
      rw [Finset.sum_insert ha, e₁, e₂, smul_add]
      abel
  obtain ⟨n₀, hn₀⟩ := hsum (decompose ℳ y).support
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨y', hy', w, e⟩ := hn₀ n hn
  exact ⟨y', hy', w, by rw [← e, sum_support_decompose]⟩

end

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
include ℳ in
private lemma eq_zero_of_X_sub_one_smul_eq_zero {y : M}
    (hy : (X i - 1 : MvPolynomial ι R) • y = 0) : y = 0 := by
  classical
  have hrec : ∀ m, (decompose ℳ y (m + 1) : M) = (X i : MvPolynomial ι R) • (decompose ℳ y m : M) := by
    intro m
    have := decompose_X_sub_one_smul_add_one ℳ i y m
    rw [hy, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero] at this
    exact (sub_eq_zero.1 this.symm).symm
  obtain ⟨N, hN⟩ := exists_decompose_eq_zero_of_lt ℳ y
  have hall : ∀ c, (decompose ℳ y c : M) = 0 := fun c =>
    eq_zero_of_X_smul_recurrence_of_vanish_below i (g := fun m => (decompose ℳ y m : M)) hN (fun m _ => hrec m)
  rw [← sum_support_decompose ℳ y]
  exact Finset.sum_eq_zero (fun j _ => hall j)

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in

theorem _root_.GlobalTheory.X_sub_one_smul_graded : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), (∀ y : M, (X i - 1 : MvPolynomial ι R) • y = 0 → y = 0) ∧ (∀ (n : ℤ) (z w : M), z ∈ ℳ n → z = (X i - 1 : MvPolynomial ι R) • w → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z = 0) ∧ (∀ y : M, ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∃ y' ∈ ℳ n, ∃ w : M, y = y' + (X i - 1 : MvPolynomial ι R) • w) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i
  exact ⟨fun y hy => eq_zero_of_X_sub_one_smul_eq_zero ℳ i hy,
    fun n z w hz h => _root_.GlobalTheory.exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul ℳ i hz h,
    fun y => _root_.GlobalTheory.exists_homogeneous_add_X_sub_one_smul ℳ i y⟩

end GlobalTheory
