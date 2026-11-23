import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing

open Matrix GlobalTheory.SUCong

namespace GlobalTheory.SUCong

theorem levMap_mul_of_goodRing {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q k : ℕ) :
    GoodRing S σ ϖ q → 1 ≤ k → ∀ (g h : GL n A), g ∈ congSU S σ H ϖ k → h ∈ congSU S σ H ϖ k →
    levMap S ϖ k ((g * h : GL n A) : Matrix n n A) =
      levMap S ϖ k (g : Matrix n n A) + levMap S ϖ k (h : Matrix n n A) := by
  intro hR hk g h hg hh
  obtain ⟨-, -, hϖS, -, hnz, -⟩ := hR
  have canc : ∀ m : ℕ, ∀ x : A, ϖ ^ m * x = 0 → x = 0 := by
    intro m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
      intro x hx; apply ih; apply hnz; rw [← mul_assoc, ← pow_succ']; exact hx
  have redAdd : ∀ a b, a ∈ S → b ∈ S → red S ϖ (a + b) = red S ϖ a + red S ϖ b := by
    intro a b ha hb
    simp only [red, dif_pos ha, dif_pos hb, dif_pos (add_mem ha hb)]
    rw [← map_add]; rfl
  have redPi : ∀ t ∈ S, red S ϖ (ϖ * t) = 0 := by
    intro t ht
    rw [red, dif_pos (mul_mem hϖS ht), Ideal.Quotient.eq_zero_iff_mem]
    have e : (⟨ϖ * t, mul_mem hϖS ht⟩ : S) = ⟨ϖ, hϖS⟩ * ⟨t, ht⟩ := rfl
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hgh := (congSU S σ H ϖ k).mul_mem hg hh
  let X : n → n → A := fun i j => Classical.choose (hg.2.2.2.2 i j)
  let Y : n → n → A := fun i j => Classical.choose (hh.2.2.2.2 i j)
  let Z : n → n → A := fun i j => Classical.choose (hgh.2.2.2.2 i j)
  have hX : ∀ i j, X i j ∈ S ∧ ((g : Matrix n n A) - 1) i j = ϖ ^ k * X i j :=
    fun i j => Classical.choose_spec (hg.2.2.2.2 i j)
  have hY : ∀ i j, Y i j ∈ S ∧ ((h : Matrix n n A) - 1) i j = ϖ ^ k * Y i j :=
    fun i j => Classical.choose_spec (hh.2.2.2.2 i j)
  have hZ : ∀ i j, Z i j ∈ S ∧ (((g * h : GL n A) : Matrix n n A) - 1) i j = ϖ ^ k * Z i j :=
    fun i j => Classical.choose_spec (hgh.2.2.2.2 i j)
  have hX2 : ∀ i j, ((g : Matrix n n A) - 1) i j = ϖ ^ k * X i j := fun i j => (hX i j).2
  have hY2 : ∀ i j, ((h : Matrix n n A) - 1) i j = ϖ ^ k * Y i j := fun i j => (hY i j).2
  have hZ2 : ∀ i j, (((g * h : GL n A) : Matrix n n A) - 1) i j = ϖ ^ k * Z i j :=
    fun i j => (hZ i j).2
  have e : ((g * h : GL n A) : Matrix n n A) - 1 = ((g : Matrix n n A) - 1) + ((h : Matrix n n A) - 1)
      + ((g : Matrix n n A) - 1) * ((h : Matrix n n A) - 1) := by
    rw [Units.val_mul]; noncomm_ring
  have key : ∀ i j, Z i j = X i j + Y i j + ϖ ^ k * ∑ l, X i l * Y l j := by
    intro i j
    have e1 := congrArg (fun M : Matrix n n A => M i j) e
    simp only [Matrix.add_apply, Matrix.mul_apply, hX2, hY2, hZ2] at e1
    have e2 : ∑ l, ϖ ^ k * X i l * (ϖ ^ k * Y l j) = ϖ ^ k * (ϖ ^ k * ∑ l, X i l * Y l j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    apply eq_of_sub_eq_zero
    apply canc k
    linear_combination e1 + e2
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  ext i j
  simp only [levMap, Matrix.add_apply]
  rw [dif_pos (hgh.2.2.2.2 i j), dif_pos (hg.2.2.2.2 i j), dif_pos (hh.2.2.2.2 i j)]
  change red S ϖ (Z i j) = red S ϖ (X i j) + red S ϖ (Y i j)
  have hT : (∑ l, X i l * Y l j) ∈ S := Subring.sum_mem _ fun l _ => mul_mem (hX i l).1 (hY l j).1
  have hPm : ϖ ^ m * ∑ l, X i l * Y l j ∈ S := mul_mem (pow_mem hϖS m) hT
  have e3 : ϖ ^ (m + 1) * ∑ l, X i l * Y l j = ϖ * (ϖ ^ m * ∑ l, X i l * Y l j) := by ring
  rw [key, redAdd _ _ (add_mem (hX i j).1 (hY i j).1) (by rw [e3]; exact mul_mem hϖS hPm),
    redAdd _ _ (hX i j).1 (hY i j).1, e3, redPi _ hPm, add_zero]

end GlobalTheory.SUCong
