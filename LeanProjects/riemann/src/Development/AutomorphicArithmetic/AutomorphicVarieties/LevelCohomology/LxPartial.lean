import Mathlib

open Finset

namespace UpperTheory.V.X

private theorem shift_sum {K : Type} [CommRing K] (F s : ℕ) (w : ℕ → K) :
    ∑ a ∈ range F, w (s + a) = ∑ a ∈ range F, w a + ∑ a ∈ range s, (w (F + a) - w a) := by
  have h1 := Finset.sum_range_add w s F
  have h2 := Finset.sum_range_add w F s
  rw [add_comm F s, h1] at h2
  rw [Finset.sum_sub_distrib]
  linear_combination h2

theorem lx_partial {K : Type} [Field K] [CharZero K] (f N : ℕ) [NeZero N] (hf : 0 < f) (hc : Nat.Coprime f N) (φ : ℕ → K)
    (hper : ∀ a, φ (a + f) = φ a) (B : Subring K) (hφ : ∀ a, φ a ∈ B) (hN : (N : K)⁻¹ ∈ B) :
    ∃ (g : ZMod N → K) (c : K), (∀ u, g u ∈ B) ∧ c ∈ B ∧
      (∀ t : ℕ, f * t ≤ N → ∀ u, g u - g (u - (f * t : ℕ)) = t * c - if u.val < f * t then φ u.val else 0) ∧
      ∀ ξ : ZMod N → K, ∑ u, ξ u = 0 → ∑ a ∈ range (f * N), φ a * ξ a * a = (f * N : ℕ) * ∑ u, ξ u * g u := by
  classical
  let ψ : ZMod N → ℕ → K := fun u a => if (a : ZMod N) = u then φ a else 0
  let A : ZMod N → K := fun u => ∑ a ∈ range (f * N), ψ u a * a
  let S : ZMod N → K := fun u => ∑ a ∈ range (f * N), ψ u a
  have hF : ((f * N : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_ne_zero hf.ne' (NeZero.ne N))
  have hf' : (f : K) ≠ 0 := Nat.cast_ne_zero.2 hf.ne'
  have hN' : (N : K) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hψB : ∀ u a, ψ u a ∈ B := by
    intro u a; simp only [ψ]; split_ifs
    · exact hφ a
    · exact B.zero_mem
  have hper' : ∀ t a, φ (f * t + a) = φ a := by
    intro t a
    induction t with
    | zero => simp
    | succ t ih => rw [show f * (t + 1) + a = (f * t + a) + f by ring, hper, ih]
  have hψ : ∀ (t : ℕ) u a, ψ u (f * t + a) = ψ (u - (f * t : ℕ)) a := by
    intro t u a
    simp only [ψ, hper']
    congr 1
    rw [Nat.cast_add, eq_sub_iff_add_eq, add_comm]
  have hψF : ∀ u a, ψ u (f * N + a) = ψ u a := by
    intro u a; rw [hψ]; simp
  have hS : ∀ (t : ℕ) u, S (u - (f * t : ℕ)) = S u := by
    intro t u
    simp only [S, ← hψ]
    rw [shift_sum (f * N) (f * t) (ψ u)]
    simp [hψF]
  have hA : ∀ (t : ℕ) u, A u - A (u - (f * t : ℕ)) = (f * t : ℕ) * S u - (f * N : ℕ) * ∑ a ∈ range (f * t), ψ u a := by
    intro t u
    have h := shift_sum (f * N) (f * t) (fun a => ψ u a * a)
    simp only [hψF] at h
    have e1 : ∑ a ∈ range (f * N), ψ u (f * t + a) * ((f * t + a : ℕ) : K) = A (u - (f * t : ℕ)) + (f * t : ℕ) * S (u - (f * t : ℕ)) := by
      simp only [A, S, hψ, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Nat.cast_add]; ring
    have e2 : ∑ a ∈ range (f * t), (ψ u a * ((f * N + a : ℕ) : K) - ψ u a * a) = (f * N : ℕ) * ∑ a ∈ range (f * t), ψ u a := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Nat.cast_add]; ring
    rw [e1, e2, hS] at h
    simp only [A] at h ⊢
    linear_combination -h
  have hgen : ∀ u : ZMod N, ∃ t : ℕ, u - (f * t : ℕ) = 0 := by
    intro u
    obtain ⟨v, hv⟩ := (ZMod.isUnit_iff_coprime f N).2 hc
    refine ⟨((v⁻¹ : (ZMod N)ˣ) * u : ZMod N).val, ?_⟩
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← hv, Units.mul_inv_cancel_left, sub_self]
  have hS0 : ∀ u, S u = S 0 := by
    intro u
    obtain ⟨t, ht⟩ := hgen u
    rw [← hS t u, ht]
  have hcB : S 0 * (N : K)⁻¹ ∈ B := B.mul_mem (B.sum_mem fun a _ => hψB _ _) hN
  have hd : ∀ (t : ℕ) u, A u / (f * N : ℕ) - A (u - (f * t : ℕ)) / (f * N : ℕ) =
      t * (S 0 * (N : K)⁻¹) - ∑ a ∈ range (f * t), ψ u a := by
    intro t u
    rw [← sub_div, hA, hS0]
    push_cast
    field_simp
  refine ⟨fun u => A u / (f * N : ℕ) - A 0 / (f * N : ℕ), S 0 * (N : K)⁻¹, ?_, hcB, ?_, ?_⟩
  · intro u
    obtain ⟨t, ht⟩ := hgen u
    have := hd t u
    rw [ht] at this
    simp only [this]
    exact B.sub_mem (B.mul_mem (natCast_mem B t) hcB) (B.sum_mem fun a _ => hψB _ _)
  · intro t ht u
    rw [sub_sub_sub_cancel_right, hd]
    congr 1
    have : ∀ a ∈ range (f * t), ψ u a = if u.val = a then φ a else 0 := by
      intro a ha
      rw [mem_range] at ha
      simp only [ψ]
      congr 1
      apply propext
      constructor
      · rintro rfl
        exact ZMod.val_natCast_of_lt (by omega)
      · rintro rfl
        exact ZMod.natCast_zmod_val u
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    simp
  · intro ξ hξ
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hξ, zero_mul, mul_zero, sub_zero, Finset.mul_sum]
    have : ∀ u, ((f * N : ℕ) : K) * (ξ u * (A u / (f * N : ℕ))) = ∑ a ∈ range (f * N), ξ u * (ψ u a * a) := by
      intro u
      rw [← Finset.mul_sum]
      simp only [A]
      field_simp
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [ψ, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, mem_univ, if_true]
    ring

end UpperTheory.V.X
