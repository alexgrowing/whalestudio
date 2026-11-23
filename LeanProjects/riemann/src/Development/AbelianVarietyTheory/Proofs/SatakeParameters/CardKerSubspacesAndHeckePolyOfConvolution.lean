import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardSubspacesOfFinrankMulCardBases

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory.KerRangeCount

theorem gaussBin_zero_right (q n : ℕ) : gaussBin q n 0 = 1 := by
  cases n <;> simp [gaussBin]

theorem gaussBin_self (q n : ℕ) : gaussBin q n n = 1 := by
  induction n with
  | zero => simp [gaussBin]
  | succ n ih => rw [gaussBin, ih, gaussBin_eq_zero q (Nat.lt_succ_self n)]; simp

theorem coeff_heckePolyOf {L : Type} [Field L] (n q : ℕ) (a : ℕ → L) (ha : ∀ j, n < j → a j = 0)
    (d : ℕ) : (heckePolyOf n q a).coeff d = (-1) ^ d * (q : L) ^ (d * (d - 1) / 2) * a d := by
  simp only [heckePolyOf, finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range] at h
    rw [ha d (by omega), mul_zero]

theorem triangle_add (i j : ℕ) :
    (j + i) * (j + i - 1) / 2 = j * (j - 1) / 2 + i * (i - 1) / 2 + j * i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [← add_assoc, Nat.triangle_succ, Nat.triangle_succ, ih]
    ring

theorem conv_eq_zero (L : Type) [Field L] (q n t : ℕ) (a : ℕ → L) (ν s : L)
    (ha : ∀ j, n < j → a j = 0) (d : ℕ) (hd : n + t < d) :
    ∑ j ∈ Finset.range (d + 1), (q : L) ^ ((n - j) * (d - j)) *
        (gaussBin q t (d - j) : L) * ν ^ (d - j) * s ^ j * a j = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hjn : n < j
  · simp [ha j hjn]
  · rw [gaussBin_eq_zero q (show t < d - j by omega)]
    simp

theorem heckePolyOf_conv (L : Type) [Field L] (q n t : ℕ) (a : ℕ → L) (ν s : L)
    (ha : ∀ j, n < j → a j = 0) :
    heckePolyOf (n + t) q (fun d => ∑ j ∈ Finset.range (d + 1), (q : L) ^ ((n - j) * (d - j)) *
        (gaussBin q t (d - j) : L) * ν ^ (d - j) * s ^ j * a j) =
      (heckePolyOf n q a).comp (C s * X) * blockPoly (ν * (q : L) ^ n) q t := by
  ext d
  rw [coeff_heckePolyOf, ← heckePolyOf_gaussBin, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun j i => ((heckePolyOf n q a).comp (C s * X)).coeff j *
        (heckePolyOf t q fun i => (ν * (q : L) ^ n) ^ i * (gaussBin q t i : L)).coeff i),
    Finset.mul_sum]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    obtain ⟨i, rfl⟩ : ∃ i, d = j + i := ⟨d - j, by omega⟩
    rw [comp_C_mul_X_coeff, coeff_heckePolyOf n q a ha, coeff_heckePolyOf t q _
      (fun j hj => by rw [gaussBin_eq_zero q hj]; simp), Nat.add_sub_cancel_left, triangle_add]
    by_cases hjn : n < j
    · simp [ha j hjn]
    obtain ⟨m, rfl⟩ : ∃ m, n = j + m := ⟨n - j, by omega⟩
    rw [Nat.add_sub_cancel_left]
    ring
  · exact conv_eq_zero L q n t a ν s ha

theorem gaussBin_add {q : ℕ} (hq : q ≠ 0) (t m e : ℕ) : gaussBin q (t + m) e =
    ∑ l ∈ Finset.range (e + 1), q ^ ((e - l) * (m - l)) * gaussBin q t (e - l) * gaussBin q m l := by
  have hz : ∀ n j, n < j → (1 : ℚ) ^ j * (gaussBin q n j : ℚ) = 0 := fun n j hj => by
    rw [gaussBin_eq_zero q hj]; simp
  have h := heckePolyOf_conv ℚ q m t (fun j => (1 : ℚ) ^ j * (gaussBin q m j : ℚ)) 1 1 (hz m)
  have hb : blockPoly (1 : ℚ) q (m + t) = blockPoly 1 q m * blockPoly (1 * (q : ℚ) ^ m) q t := by
    simp only [blockPoly, Finset.prod_range_add, pow_add, mul_assoc]
  rw [heckePolyOf_gaussBin, C_1, one_mul X, comp_X, ← hb, ← heckePolyOf_gaussBin] at h
  have h2 := congrArg (fun p => p.coeff e) h
  rw [coeff_heckePolyOf _ _ _ (conv_eq_zero ℚ q m t _ 1 1 (hz m)), coeff_heckePolyOf _ _ _ (hz _)] at h2
  have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have h3 := mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hq')) h2
  simp only [one_pow, mul_one, one_mul] at h3
  rw [add_comm t m]
  apply Nat.cast_injective (R := ℚ)
  rw [← h3]
  push_cast
  exact Finset.sum_congr rfl fun l _ => by rw [mul_comm (m - l)]

theorem gaussBin_succ_succ' {q : ℕ} (hq : q ≠ 0) (n k : ℕ) :
    gaussBin q (n + 1) (k + 1) = q ^ (n - k) * gaussBin q n k + gaussBin q n (k + 1) := by
  rw [add_comm n 1, gaussBin_add hq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp [gaussBin_zero_right, gaussBin_self]
  · intro l hl
    rw [Finset.mem_range] at hl
    rw [gaussBin_eq_zero q (show 1 < k + 1 - l by omega)]
    simp

theorem gaussBin_symm {q : ℕ} (hq : q ≠ 0) : ∀ N a b : ℕ, a + b = N → gaussBin q N a = gaussBin q N b := by
  intro N
  induction N with
  | zero =>
    intro a b h
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    rfl
  | succ N ih =>
    intro a b h
    cases a with
    | zero =>
      obtain rfl : b = N + 1 := by omega
      rw [gaussBin_zero_right, gaussBin_self]
    | succ a =>
      cases b with
      | zero =>
        obtain rfl : a = N := by omega
        rw [gaussBin_zero_right, gaussBin_self]
      | succ b =>
        rw [gaussBin, gaussBin_succ_succ' hq, ih a (b + 1) (by omega), ih (a + 1) b (by omega),
          show N - b = a + 1 by omega, add_comm]

theorem prod_succ_succ (q : ℤ) (n a : ℕ) : ∏ i ∈ Finset.range (a + 1), (q ^ (n + 1) - q ^ i) =
    (q ^ (n + 1) - 1) * q ^ a * ∏ i ∈ Finset.range a, (q ^ n - q ^ i) := by
  rw [Finset.prod_range_succ', Finset.prod_congr rfl
    (fun i _ => (by ring : q ^ (n + 1) - q ^ (i + 1) = q * (q ^ n - q ^ i))), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_range]
  ring

theorem gaussBin_mul_prod (q n a : ℕ) :
    (gaussBin q n a : ℤ) * ∏ i ∈ Finset.range a, ((q : ℤ) ^ a - q ^ i) =
      ∏ i ∈ Finset.range a, ((q : ℤ) ^ n - q ^ i) := by
  induction n generalizing a with
  | zero =>
    cases a with
    | zero => simp [gaussBin]
    | succ a => simp [gaussBin, Finset.prod_range_succ']
  | succ n ih =>
    cases a with
    | zero => simp [gaussBin]
    | succ a =>
      have h1 := ih a
      have h2 := ih (a + 1)
      rw [Finset.prod_range_succ (fun i => (q : ℤ) ^ n - q ^ i), prod_succ_succ] at h2
      rw [gaussBin, prod_succ_succ, prod_succ_succ]
      push_cast
      linear_combination ((q : ℤ) ^ (a + 1) - 1) * q ^ a * h1 + (q : ℤ) ^ (a + 1) * h2

theorem cast_prod_sub {q : ℕ} (hq : q ≠ 0) {n a : ℕ} (h : a ≤ n) :
    ((∏ i ∈ Finset.range a, (q ^ n - q ^ i) : ℕ) : ℤ) = ∏ i ∈ Finset.range a, ((q : ℤ) ^ n - q ^ i) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Nat.cast_sub (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hq) (by omega))]
  push_cast
  rfl

section Count

variable {k V : Type} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem card_subspaces (i : ℕ) : Nat.card {W : Submodule k V // Module.finrank k W = i} =
    gaussBin (Fintype.card k) (Module.finrank k V) i := by
  by_cases hi : i ≤ Module.finrank k V
  · have h := GlobalTheory.SubspaceNumber.card_subspaces_mul k V i hi
    rw [Nat.card_eq_fintype_card (α := k)] at h
    have h1 := congrArg (Nat.cast : ℕ → ℤ) h
    rw [Nat.cast_mul, cast_prod_sub Fintype.card_ne_zero le_rfl, cast_prod_sub Fintype.card_ne_zero hi,
      ← gaussBin_mul_prod (Fintype.card k) (Module.finrank k V) i] at h1
    refine Nat.cast_injective (R := ℤ) (mul_right_cancel₀ ?_ h1)
    refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
    rw [Finset.mem_range] at hj
    have h2 : (1 : ℤ) < Fintype.card k := by exact_mod_cast Fintype.one_lt_card
    exact (sub_pos.2 (pow_lt_pow_right₀ h2 hj)).ne'
  · have : IsEmpty {W : Submodule k V // Module.finrank k W = i} :=
      ⟨fun W => by have := W.1.finrank_le; have := W.2; omega⟩
    rw [Nat.card_of_isEmpty, gaussBin_eq_zero _ (by omega)]

theorem card_below (A : Submodule k V) (i : ℕ) :
    Nat.card {W : Submodule k V // Module.finrank k W = i ∧ W ≤ A} =
      gaussBin (Fintype.card k) (Module.finrank k A) i := by
  rw [← card_subspaces (k := k) (V := A) i]
  refine (Nat.card_eq_of_bijective
    (fun W : {W : Submodule k A // Module.finrank k W = i} =>
      (⟨W.1.map A.subtype, by rw [Submodule.finrank_map_subtype_eq]; exact W.2,
        Submodule.map_subtype_le _ _⟩ :
        {W : Submodule k V // Module.finrank k W = i ∧ W ≤ A})) ⟨?_, ?_⟩).symm
  · intro W W' h
    exact Subtype.ext (Submodule.map_injective_of_injective A.injective_subtype (congrArg Subtype.val h))
  · rintro ⟨W, h1, h2⟩
    have e : (W.comap A.subtype).map A.subtype = W := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 h2]
    refine ⟨⟨W.comap A.subtype, ?_⟩, Subtype.ext e⟩
    rw [← Submodule.finrank_map_subtype_eq, e, h1]

theorem finrank_comap_mkQ (A : Submodule k V) (W : Submodule k (V ⧸ A)) :
    Module.finrank k (W.comap A.mkQ) = Module.finrank k A + Module.finrank k W := by
  have h1 := (W.comap A.mkQ).finrank_quotient_add_finrank
  have h2 := A.finrank_quotient_add_finrank
  have h3 := W.finrank_quotient_add_finrank
  have hle : A ≤ W.comap A.mkQ := Submodule.le_comap_mkQ A W
  have e : (W.comap A.mkQ).map A.mkQ = W := Submodule.map_comap_eq_of_surjective A.mkQ_surjective W
  have h4 := (Submodule.quotientQuotientEquivQuotient A (W.comap A.mkQ) hle).finrank_eq
  rw [e] at h4
  omega

theorem card_above (A : Submodule k V) (l : ℕ) :
    Nat.card {W : Submodule k V // Module.finrank k W = Module.finrank k A + l ∧ A ≤ W} =
      gaussBin (Fintype.card k) (Module.finrank k V - Module.finrank k A) l := by
  have h2 := A.finrank_quotient_add_finrank
  rw [show Module.finrank k V - Module.finrank k A = Module.finrank k (V ⧸ A) by omega,
    ← card_subspaces (k := k) (V := V ⧸ A) l]
  refine (Nat.card_eq_of_bijective
    (fun W : {W : Submodule k (V ⧸ A) // Module.finrank k W = l} =>
      (⟨W.1.comap A.mkQ, by rw [finrank_comap_mkQ, W.2], Submodule.le_comap_mkQ A W.1⟩ :
        {W : Submodule k V // Module.finrank k W = Module.finrank k A + l ∧ A ≤ W})) ⟨?_, ?_⟩).symm
  · intro W W' h
    exact Subtype.ext (Submodule.comap_injective_of_surjective A.mkQ_surjective (congrArg Subtype.val h))
  · rintro ⟨W, h1, h2⟩
    have e : (W.map A.mkQ).comap A.mkQ = W := by
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 h2]
    refine ⟨⟨W.map A.mkQ, ?_⟩, Subtype.ext e⟩
    have := finrank_comap_mkQ A (W.map A.mkQ)
    rw [e, h1] at this
    omega

theorem card_above_eq_zero (A : Submodule k V) {j : ℕ} (hj : j < Module.finrank k A) :
    Nat.card {W : Submodule k V // Module.finrank k W = j ∧ A ≤ W} = 0 := by
  have : IsEmpty {W : Submodule k V // Module.finrank k W = j ∧ A ≤ W} :=
    ⟨fun W => by have := Submodule.finrank_mono W.2.2; have := W.2.1; omega⟩
  exact Nat.card_of_isEmpty

end Count

theorem card_ker_eq_sum (k U U' : Type) [Field k] [Fintype k] [AddCommGroup U] [Module k U]
    [FiniteDimensional k U] [AddCommGroup U'] [Module k U'] [FiniteDimensional k U'] (n t d : ℕ)
    (f : U →ₗ[k] U') (hU : Module.finrank k U = n + t) (hU' : Module.finrank k U' = n) :
    Nat.card {W : Submodule k U // Module.finrank k W + d = n + t ∧ W ≤ LinearMap.ker f} =
      ∑ j ∈ Finset.range (d + 1), Fintype.card k ^ ((n - j) * (d - j)) *
        gaussBin (Fintype.card k) t (d - j) *
        Nat.card {W' : Submodule k U' // Module.finrank k W' = j ∧ LinearMap.range f ≤ W'} := by
  have hrk := f.finrank_range_add_finrank_ker
  have hle := (LinearMap.range f).finrank_le
  by_cases hd : d < Module.finrank k (LinearMap.range f)
  · have : IsEmpty {W : Submodule k U // Module.finrank k W + d = n + t ∧ W ≤ LinearMap.ker f} :=
      ⟨fun W => by have := Submodule.finrank_mono W.2.2; have := W.2.1; omega⟩
    rw [Nat.card_of_isEmpty, Finset.sum_eq_zero]
    intro j hj
    rw [Finset.mem_range] at hj
    rw [card_above_eq_zero _ (by omega), mul_zero]
  obtain ⟨e, he⟩ : ∃ e, d = Module.finrank k (LinearMap.range f) + e := Nat.exists_eq_add_of_le (by omega)
  obtain ⟨m, hm⟩ : ∃ m, n = Module.finrank k (LinearMap.range f) + m := Nat.exists_eq_add_of_le (by omega)
  have hker : Module.finrank k (LinearMap.ker f) = t + m := by omega
  have hL : Nat.card {W : Submodule k U // Module.finrank k W + d = n + t ∧ W ≤ LinearMap.ker f} =
      gaussBin (Fintype.card k) (t + m) e := by
    by_cases hem : e ≤ t + m
    · rw [← gaussBin_symm Fintype.card_ne_zero (t + m) (t + m - e) e (by omega), ← hker, ← card_below]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun W => and_congr_left fun _ => by omega)
    · have : IsEmpty {W : Submodule k U // Module.finrank k W + d = n + t ∧ W ≤ LinearMap.ker f} :=
        ⟨fun W => by have := W.2.1; omega⟩
      rw [Nat.card_of_isEmpty, gaussBin_eq_zero _ (by omega)]
  rw [hL, gaussBin_add Fintype.card_ne_zero, show d + 1 = Module.finrank k (LinearMap.range f) + (e + 1) by omega,
    Finset.sum_range_add _ (Module.finrank k (LinearMap.range f)), Finset.sum_eq_zero (s := Finset.range (Module.finrank k (LinearMap.range f))),
    zero_add]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [card_above, hU', show n - Module.finrank k (LinearMap.range f) = m by omega,
      show n - (Module.finrank k (LinearMap.range f) + l) = m - l by omega,
      show d - (Module.finrank k (LinearMap.range f) + l) = e - l by omega, mul_comm (m - l)]
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [card_above_eq_zero _ hj, mul_zero]

theorem card_ker_and_heckePolyOf_conv : (∀ (k U U' : Type) [Field k] [Fintype k] [AddCommGroup U] [Module k U] [FiniteDimensional k U] [AddCommGroup U'] [Module k U'] [FiniteDimensional k U'] (n t d : ℕ) (f : U →ₗ[k] U'), Module.finrank k U = n + t → Module.finrank k U' = n → Nat.card {W : Submodule k U // Module.finrank k W + d = n + t ∧ W ≤ LinearMap.ker f} = ∑ j ∈ Finset.range (d + 1), Fintype.card k ^ ((n - j) * (d - j)) * gaussBin (Fintype.card k) t (d - j) * Nat.card {W' : Submodule k U' // Module.finrank k W' = j ∧ LinearMap.range f ≤ W'}) ∧ ∀ (L : Type) [Field L] (q n t : ℕ) (a : ℕ → L) (ν s : L), (∀ j, n < j → a j = 0) → heckePolyOf (n + t) q (fun d => ∑ j ∈ Finset.range (d + 1), (q : L) ^ ((n - j) * (d - j)) * (gaussBin q t (d - j) : L) * ν ^ (d - j) * s ^ j * a j) = (heckePolyOf n q a).comp (C s * X) * blockPoly (ν * (q : L) ^ n) q t :=
  ⟨card_ker_eq_sum, heckePolyOf_conv⟩

end GlobalTheory.KerRangeCount
