import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

namespace UpperTheory.V.AlgebraTools

private noncomputable def ilcP (B : Type) [CommRing B] : ℕ → B[X]
  | 0 => X
  | k + 1 => 3 * ilcP B k ^ 2 - 2 * ilcP B k ^ 3

end UpperTheory.V.AlgebraTools

open UpperTheory.V.AlgebraTools in
theorem UpperTheory.V.AlgebraTools.idem_lift_complete :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (I : Ideal B) [IsAdicComplete I E] (z : E) (M : ℕ), (z * z - z) ^ M ∈ I • (⊤ : Submodule B E) → ∃ e : E, IsIdempotentElem e ∧ ∀ N : ℕ, ∃ q : B[X], e - (z + (z * z - z) * aeval z q) ∈ I ^ N • (⊤ : Submodule B E) := by
  intro B E _ _ _ I _ z M hM
  set S : ℕ → Submodule B E := fun n => I ^ n • (⊤ : Submodule B E) with hS
  have L2r : ∀ n (x y : E), x ∈ I ^ n • (⊤ : Submodule B E) →
      x * y ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n x y hx
    refine Submodule.smul_induction_on (p := fun x => x * y ∈ I ^ n • (⊤ : Submodule B E)) hx
      (fun a ha m _ => ?_) (fun x1 x2 h1 h2 => ?_)
    · rw [smul_mul_assoc]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [add_mul]
      exact add_mem h1 h2
  have L2l : ∀ n (x y : E), x ∈ I ^ n • (⊤ : Submodule B E) →
      y * x ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n x y hx
    refine Submodule.smul_induction_on (p := fun x => y * x ∈ I ^ n • (⊤ : Submodule B E)) hx
      (fun a ha m _ => ?_) (fun x1 x2 h1 h2 => ?_)
    · rw [mul_smul_comm]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [mul_add]
      exact add_mem h1 h2
  have L3 : ∀ n (x w : E), x ∈ I • (⊤ : Submodule B E) → w ∈ I ^ n • (⊤ : Submodule B E) →
      x * w ∈ I ^ (n + 1) • (⊤ : Submodule B E) := by
    intro n x w hx hw
    refine Submodule.smul_induction_on
      (p := fun x => x * w ∈ I ^ (n + 1) • (⊤ : Submodule B E)) hx
      (fun a ha m _ => ?_) (fun x1 x2 h1 h2 => ?_)
    · rw [smul_mul_assoc]
      have h := Submodule.smul_mem_smul ha (L2l n w m hw)
      rwa [← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_succ'] at h
    · rw [add_mul]
      exact add_mem h1 h2
  have Lpow : ∀ n (x : E), x ∈ I • (⊤ : Submodule B E) → x ^ n ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n x hx
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    | succ n ih =>
      rw [pow_succ' x n]
      exact L3 n x _ hx ih
  have Mem : ∀ n k, M * n ≤ 2 ^ k → ∀ y : E,
      (z * z - z) ^ (2 ^ k) * y ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n k hk y
    have h : (z * z - z) ^ (2 ^ k) = ((z * z - z) ^ M) ^ n * (z * z - z) ^ (2 ^ k - M * n) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk]
    rw [h, mul_assoc]
    exact L2r _ _ _ (Lpow n _ hM)
  have hk2 : ∀ k : ℕ, k ≤ 2 ^ k := fun k => (Nat.lt_two_pow_self).le
  have PoincareLelongAlt : ∀ k, ∃ Q : B[X], ilcP B k = X + (X * X - X) * Q := by
    intro k
    induction k with
    | zero => exact ⟨0, by rw [ilcP]; ring⟩
    | succ k ih =>
      obtain ⟨Q, hQ⟩ := ih
      refine ⟨Q - (1 + 2 * X * Q + (X * X - X) * Q ^ 2 - Q) * (2 * (X + (X * X - X) * Q) - 1), ?_⟩
      rw [ilcP, hQ]
      ring
  have ProjectiveLineTwo : ∀ k, ∃ W : B[X], ilcP B k * ilcP B k - ilcP B k = (X * X - X) ^ (2 ^ k) * W := by
    intro k
    induction k with
    | zero => exact ⟨1, by rw [ilcP]; ring⟩
    | succ k ih =>
      obtain ⟨W, hW⟩ := ih
      have hid : ∀ P : B[X], (3 * P ^ 2 - 2 * P ^ 3) * (3 * P ^ 2 - 2 * P ^ 3) -
          (3 * P ^ 2 - 2 * P ^ 3) = (P * P - P) ^ 2 * (4 * (P * P - P) - 3) := fun P => by ring
      refine ⟨W ^ 2 * (4 * (X * X - X) ^ (2 ^ k) * W - 3), ?_⟩
      rw [ilcP, hid, hW, pow_succ 2 k, pow_mul]
      ring
  have PL3 : ∀ k, ∃ V : B[X], ilcP B (k + 1) - ilcP B k = (X * X - X) ^ (2 ^ k) * V := by
    intro k
    obtain ⟨W, hW⟩ := ProjectiveLineTwo k
    refine ⟨-(W * (2 * ilcP B k - 1)), ?_⟩
    rw [ilcP]
    linear_combination (-(2 * ilcP B k - 1)) * hW
  have PL4 : ∀ k j, ∃ V : B[X], ilcP B (k + j) - ilcP B k = (X * X - X) ^ (2 ^ k) * V := by
    intro k j
    induction j with
    | zero => exact ⟨0, by simp⟩
    | succ j ih =>
      obtain ⟨V0, hV0⟩ := ih
      obtain ⟨V1, hV1⟩ := PL3 (k + j)
      have hpow : (X * X - X : B[X]) ^ (2 ^ (k + j)) =
          (X * X - X) ^ (2 ^ k) * (X * X - X) ^ (2 ^ (k + j) - 2 ^ k) := by
        rw [← pow_add, Nat.add_sub_cancel' (Nat.pow_le_pow_right (by norm_num) (by omega))]
      refine ⟨(X * X - X) ^ (2 ^ (k + j) - 2 ^ k) * V1 + V0, ?_⟩
      rw [show k + (j + 1) = k + j + 1 by omega]
      linear_combination hV1 + hV0 + V1 * hpow
  have hD : aeval z (X * X - X : B[X]) = z * z - z := by simp
  let f : ℕ → E := fun n => aeval z (ilcP B (M * n))
  have hdiff : ∀ k j, ∃ V : B[X], aeval z (ilcP B (k + j)) - aeval z (ilcP B k) =
      (z * z - z) ^ (2 ^ k) * aeval z V := by
    intro k j
    obtain ⟨V, hV⟩ := PL4 k j
    refine ⟨V, ?_⟩
    have h := congrArg (aeval z) hV
    rwa [map_sub, map_mul, map_pow, hD] at h
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (I ^ m • (⊤ : Submodule B E))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    obtain ⟨V, hV⟩ := hdiff (M * m) (M * n - M * m)
    rw [Nat.add_sub_cancel' (Nat.mul_le_mul_left M hmn)] at hV
    have h : f m - f n = -((z * z - z) ^ (2 ^ (M * m)) * aeval z V) := by
      rw [← hV]
      simp only [f]
      abel
    rw [h]
    exact neg_mem (Mem m (M * m) (hk2 _) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I E) hcauchy
  have hd : ∀ n, L - f n ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n
    have h := (SModEq.sub_mem).mp (hL n)
    rw [← neg_sub]
    exact neg_mem h
  have hsq : ∀ n, f n * f n - f n ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n
    obtain ⟨W, hW⟩ := ProjectiveLineTwo (M * n)
    have h := congrArg (aeval z) hW
    rw [map_sub, map_mul, map_mul, map_pow, hD] at h
    simp only [f]
    rw [h]
    exact Mem n (M * n) (hk2 _) _
  have hidem : IsIdempotentElem L := by
    have h0 : L * L - L = 0 := by
      apply IsHausdorff.haus (inferInstance : IsHausdorff I E)
      intro n
      rw [SModEq.sub_mem, sub_zero]
      have e1 : L * L - L = (f n * f n - f n) + (f n * (L - f n) + (L - f n) * f n +
          (L - f n) * (L - f n) - (L - f n)) := by noncomm_ring
      rw [e1]
      have hdn := hd n
      exact add_mem (hsq n) (sub_mem (add_mem (add_mem (L2l _ _ _ hdn) (L2r _ _ _ hdn))
        (L2r _ _ _ hdn)) hdn)
    exact sub_eq_zero.mp h0
  refine ⟨L, hidem, fun N => ?_⟩
  obtain ⟨Q, hQ⟩ := PoincareLelongAlt (M * N)
  refine ⟨Q, ?_⟩
  have h : f N = z + (z * z - z) * aeval z Q := by
    simp only [f]
    rw [hQ, map_add, map_mul, hD, aeval_X]
  rw [← h]
  exact hd N
