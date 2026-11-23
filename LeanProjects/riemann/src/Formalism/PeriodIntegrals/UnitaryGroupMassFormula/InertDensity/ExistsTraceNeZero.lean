import Mathlib

open Finset Polynomial

namespace DensInertW

variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

theorem card_L (h2 : Module.finrank K L = 2) : Fintype.card L = Fintype.card K ^ 2 := by
  rw [Module.card_eq_pow_finrank (K := K) (V := L), h2]

omit [Fintype L] [Algebra K L] in
theorem one_lt_q : 1 < Fintype.card K := Fintype.one_lt_card

variable (K) in

def conj : L →+* L := (FiniteField.frobeniusAlgHom K L).toRingHom

omit [Fintype L] in
theorem conj_apply (x : L) : conj K x = x ^ Fintype.card K := rfl

omit [Fintype L] in
theorem frob_add (x y : L) :
    (x + y) ^ Fintype.card K = x ^ Fintype.card K + y ^ Fintype.card K :=
  map_add (conj K) x y

omit [Fintype L] in
theorem frob_sub (x y : L) :
    (x - y) ^ Fintype.card K = x ^ Fintype.card K - y ^ Fintype.card K :=
  map_sub (conj K) x y

omit [Fintype L] in
theorem frob_sum {ι : Type} (s : Finset ι) (f : ι → L) :
    (∑ i ∈ s, f i) ^ Fintype.card K = ∑ i ∈ s, f i ^ Fintype.card K :=
  map_sum (conj K) f s

omit [Fintype L] in
theorem frob_algebraMap (a : K) :
    (algebraMap K L a) ^ Fintype.card K = algebraMap K L a := by
  rw [← map_pow, FiniteField.pow_card]

theorem frob_frob (h2 : Module.finrank K L = 2) (x : L) :
    (x ^ Fintype.card K) ^ Fintype.card K = x := by
  rw [← pow_mul, ← sq, ← card_L h2, FiniteField.pow_card]

theorem conj_conj (h2 : Module.finrank K L = 2) (x : L) : conj K (conj K x) = x :=
  frob_frob h2 x

theorem card_fixed [DecidableEq L] : #{x : L | x ^ Fintype.card K = x} = Fintype.card K := by
  have hq := one_lt_q (K := K)
  apply le_antisymm
  · have hne := FiniteField.X_pow_card_sub_X_ne_zero L hq
    calc #{x : L | x ^ Fintype.card K = x}
        ≤ ((X ^ Fintype.card K - X : L[X]).roots.toFinset).card := by
          apply card_le_card
          intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx
          rw [Multiset.mem_toFinset, mem_roots hne]
          simp [hx]
      _ ≤ Multiset.card (X ^ Fintype.card K - X : L[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ Fintype.card K - X : L[X]).natDegree := card_roots' _
      _ = Fintype.card K := FiniteField.X_pow_card_sub_X_natDegree_eq L hq
  · calc Fintype.card K = (univ.image (algebraMap K L)).card := by
          rw [card_image_of_injective _ (algebraMap K L).injective, card_univ]
      _ ≤ _ := by
          apply card_le_card
          intro x hx
          obtain ⟨a, -, rfl⟩ := mem_image.mp hx
          simp [frob_algebraMap]

theorem norm_fixed (h2 : Module.finrank K L = 2) (x : L) :
    (x ^ (Fintype.card K + 1)) ^ Fintype.card K = x ^ (Fintype.card K + 1) := by
  rw [← pow_mul, mul_comm, pow_mul, pow_succ, frob_frob h2, ← pow_succ']

omit [Fintype K] [Algebra K L] in
theorem card_root_le [DecidableEq L] (n : ℕ) (a : L) : #{x : L | x ^ (n + 1) = a} ≤ n + 1 := by
  calc #{x : L | x ^ (n + 1) = a} ≤ (nthRoots (n + 1) a).toFinset.card := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        rw [Multiset.mem_toFinset, mem_nthRoots (Nat.succ_pos n)]
        exact hx
    _ ≤ Multiset.card (nthRoots (n + 1) a) := Multiset.toFinset_card_le _
    _ ≤ n + 1 := card_nthRoots _ _

theorem card_norm_fibre [DecidableEq L] (h2 : Module.finrank K L = 2) (a : L) (ha0 : a ≠ 0)
    (haq : a ^ Fintype.card K = a) :
    #{x : L | x ^ (Fintype.card K + 1) = a} = Fintype.card K + 1 := by
  set q := Fintype.card K with hqdef
  have hq : 1 < q := one_lt_q
  set F : Finset L := {b : L | b ≠ 0 ∧ b ^ q = b} with hF
  have hFcard : F.card + 1 = q := by
    have : ({x : L | x ^ q = x} : Finset L) = insert 0 F := by
      ext b
      simp only [hF, mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro h
        by_cases hb : b = 0
        · exact Or.inl hb
        · exact Or.inr ⟨hb, h⟩
      · rintro (rfl | ⟨-, h⟩)
        · exact zero_pow (by omega)
        · exact h
    have h0 : (0 : L) ∉ F := by simp [hF]
    rw [← card_insert_of_notMem h0, ← this]
    exact card_fixed

  have hsum : ∑ b ∈ F, #{x : L | x ^ (q + 1) = b} = q ^ 2 - 1 := by
    have hmaps : ∀ x ∈ (univ.erase (0 : L)), x ^ (q + 1) ∈ F := by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_mem_erase hx
      simp only [hF, mem_filter, mem_univ, true_and]
      exact ⟨pow_ne_zero _ hx0, norm_fixed h2 x⟩
    rw [← card_L h2, ← card_univ, ← card_erase_of_mem (mem_univ (0 : L)),
      card_eq_sum_card_fiberwise hmaps]
    refine sum_congr rfl (fun b hb => ?_)
    have hb0 : b ≠ 0 := by simp only [hF, mem_filter, mem_univ, true_and] at hb; exact hb.1
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    constructor
    · intro h
      refine ⟨?_, h⟩
      intro hx
      subst hx
      exact hb0 (by rw [← h, zero_pow (by omega)])
    · exact fun h => h.2
  have hle : ∀ b ∈ F, #{x : L | x ^ (q + 1) = b} ≤ q + 1 := fun b _ => card_root_le q b
  have haF : a ∈ F := by simp [hF, ha0, haq]
  by_contra hne
  have hlt : #{x : L | x ^ (q + 1) = a} < q + 1 := lt_of_le_of_ne (hle a haF) hne
  have := sum_lt_sum hle ⟨a, haF, hlt⟩
  rw [hsum, sum_const, smul_eq_mul] at this
  have e : F.card = q - 1 := by omega
  rw [e] at this
  have e2 : (q - 1) * (q + 1) = q ^ 2 - 1 := by
    have h1 : 1 ≤ q := by omega
    have h3 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h3]
    ring
  omega

omit [Fintype K] [Algebra K L] in
theorem card_norm_zero [DecidableEq L] (n : ℕ) : #{x : L | x ^ (n + 1) = 0} = 1 := by
  rw [card_eq_one]
  refine ⟨0, ?_⟩
  ext x
  simp

theorem exists_trace_ne_zero (h2 : Module.finrank K L = 2) (z : L) (hz : z ≠ 0) :
    ∃ c : L, c * z + (c * z) ^ Fintype.card K ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  have ht : ∀ t : L, t + t ^ Fintype.card K = 0 := by
    intro t
    have := hall (t / z)
    rwa [div_mul_cancel₀ t hz] at this
  have h11 : (1 : L) + 1 = 0 := by simpa using ht 1
  have hfix : ∀ t : L, t ^ Fintype.card K = t := by
    intro t
    have e1 : t ^ Fintype.card K = -t := eq_neg_of_add_eq_zero_right (ht t)
    have e2 : -t = t := by
      have : t + t = 0 := by rw [← two_mul, show (2 : L) = 1 + 1 by norm_num, h11, zero_mul]
      exact (neg_eq_of_add_eq_zero_right this)
    rw [e1, e2]
  have hc := card_fixed (K := K) (L := L)
  have huniv : ({x : L | x ^ Fintype.card K = x} : Finset L) = univ := by
    ext t; simp [hfix t]
  rw [huniv, card_univ, card_L h2] at hc
  have hq := one_lt_q (K := K)
  have : Fintype.card K ^ 2 > Fintype.card K := by nlinarith
  omega

end DensInertW
