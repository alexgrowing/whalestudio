import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsOfEmbedding
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexStabilizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubOneMulSumEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowPrimeStep

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.CorShap

section Cg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {l n : ℕ}

theorem nat_mem (k : ℕ) : (k : Ω) ∈ A := by simpa using A.toSubring.natCast_mem k

theorem int_mem (k : ℤ) : (k : Ω) ∈ A := by simpa using A.toSubring.intCast_mem k

theorem cg_refl (x : Ω) : CgA A l n x x := ⟨0, A.zero_mem, by simp⟩

theorem cg_symm {x y : Ω} (h : CgA A l n x y) : CgA A l n y x := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨-z, neg_mem hz, by rw [mul_neg, ← e]; ring⟩

theorem cg_trans {x y w : Ω} (h1 : CgA A l n x y) (h2 : CgA A l n y w) : CgA A l n x w := by
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  exact ⟨a + b, add_mem ha hb, by rw [mul_add, ← e1, ← e2]; ring⟩

theorem cg_add {x y x' y' : Ω} (h1 : CgA A l n x y) (h2 : CgA A l n x' y') : CgA A l n (x + x') (y + y') := by
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  exact ⟨a + b, add_mem ha hb, by rw [mul_add, ← e1, ← e2]; ring⟩

theorem cg_sub {x y x' y' : Ω} (h1 : CgA A l n x y) (h2 : CgA A l n x' y') : CgA A l n (x - x') (y - y') := by
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  exact ⟨a - b, sub_mem ha hb, by rw [mul_sub, ← e1, ← e2]; ring⟩

theorem cg_mul {x y : Ω} (c : Ω) (hc : c ∈ A) (h : CgA A l n x y) : CgA A l n (c * x) (c * y) := by
  obtain ⟨a, ha, e⟩ := h
  exact ⟨c * a, mul_mem hc ha, by rw [← mul_sub, e]; ring⟩

theorem cg_congr {x y x' y' : Ω} (h : CgA A l n x y) (hx : x = x') (hy : y = y') : CgA A l n x' y' := hx ▸ hy ▸ h

theorem cg_sum {ι : Type*} (s : Finset ι) (f g : ι → Ω) (h : ∀ i ∈ s, CgA A l n (f i) (g i)) :
    CgA A l n (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using cg_refl (A := A) (l := l) (n := n) (0 : Ω)
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact cg_add (h a (Finset.mem_cons_self a s)) (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

theorem cg_map {s : Ω ≃ₐ[ℚ] Ω} (hs : Stab A s) {x y : Ω} (h : CgA A l n x y) : CgA A l n (s x) (s y) := by
  obtain ⟨a, ha, e⟩ := h
  exact ⟨s a, (hs a).2 ha, by rw [← map_sub, e, map_mul, map_pow, map_natCast]⟩

theorem cg_nat {a b : ℕ} (h : (a : ZMod (l ^ n)) = b) : CgA A l n (a : Ω) (b : Ω) := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  refine ⟨((a / l ^ n : ℕ) : Ω) - ((b / l ^ n : ℕ) : Ω), sub_mem (nat_mem _) (nat_mem _), ?_⟩
  have e1 : (a : Ω) = ((a % l ^ n : ℕ) : Ω) + (l : Ω) ^ n * ((a / l ^ n : ℕ) : Ω) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  have e2 : (b : Ω) = ((b % l ^ n : ℕ) : Ω) + (l : Ω) ^ n * ((b / l ^ n : ℕ) : Ω) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  rw [e1, e2, h]; ring

end Cg

theorem stab_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {s t : Ω ≃ₐ[ℚ] Ω} (hs : Stab A s)
    (ht : Stab A t) : Stab A (s * t) := fun x => by rw [AlgEquiv.mul_apply, hs, ht]

theorem stab_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {s : Ω ≃ₐ[ℚ] Ω} (hs : Stab A s) :
    Stab A s⁻¹ := fun x => by
  rw [← hs (s⁻¹ x), ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem stab_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {s : Ω ≃ₐ[ℚ] Ω} (hs : Stab A s) (k : ℕ) :
    Stab A (s ^ k) := by
  induction k with
  | zero => intro x; simp
  | succ k ih => rw [pow_succ]; exact stab_mul ih hs

theorem mem_of_inZl {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring Ω) (hp : ((p : ℕ) : Ω) ∈ A.nonunits) (L : ℕ) (F : Ω) (hF : InZl ε p L F) : F ∈ A := by
  have hpp : p.Prime := Fact.out
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hζ := IsNTr.isPrimitiveRoot_zt ε p L
  have hN : 0 < p ^ L := pow_pos hpp.pos L
  have hz : zt ε p L ∈ A := by
    rcases A.mem_or_inv_mem (zt ε p L) with h | h
    · exact h
    · have e : zt ε p L = (zt ε p L)⁻¹ ^ (p ^ L - 1) := by
        rw [inv_pow]; apply eq_inv_of_mul_eq_one_left; rw [← pow_succ', Nat.sub_add_cancel hN, hζ.pow_eq_one]
      rw [e]; exact pow_mem h _
  obtain ⟨D, hD, hDF⟩ := hF
  have hcl : (D : Ω) * F ∈ A :=
    (Subring.closure_le (t := A.toSubring)).2 (Set.singleton_subset_iff.2 hz) hDF
  have hcop : IsCoprime (D : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hpp).2 hD).symm
  obtain ⟨u, v, huv⟩ := hcop
  have e : (u : Ω) * D + v * p = 1 := by exact_mod_cast congrArg (fun x : ℤ => (x : Ω)) huv
  have hv : A.valuation (D : Ω) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).2 (nat_mem D)) ?_
    by_contra hlt
    push_neg at hlt
    have hp1 : A.valuation (p : Ω) < 1 := A.mem_nonunits_iff.1 hp
    have hu1 : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (int_mem u)
    have hv1 : A.valuation (v : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (int_mem v)
    have h1 : A.valuation ((u : Ω) * D + v * p) < 1 := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hu1) hlt
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hv1) hp1
    rw [e, map_one] at h1
    exact lt_irrefl _ h1
  have hD0 : (D : Ω) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hDi : (D : Ω)⁻¹ ∈ A := (A.valuation_le_one_iff _).1 (by rw [map_inv₀, hv, inv_one])
  have := mul_mem hDi hcl
  rwa [inv_mul_cancel_left₀ hD0] at this

section Lev

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem lc_exists (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (M : ℕ) :
    ∃ e : (Ω ≃ₐ[ℚ] Ω) → ZMod (p ^ M), ∀ g, g (zt ε p M) = zt ε p M ^ (e g).val := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hζ := IsNTr.isPrimitiveRoot_zt ε p M
  have : ∀ g : Ω ≃ₐ[ℚ] Ω, ∃ t : ZMod (p ^ M), g (zt ε p M) = zt ε p M ^ t.val := fun g => by
    obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one (ξ := g (zt ε p M)) (by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨i, by rw [ZMod.val_natCast_of_lt hi, he]⟩
  exact ⟨fun g => (this g).choose, fun g => (this g).choose_spec⟩

theorem lc_mul (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (M : ℕ) (e : (Ω ≃ₐ[ℚ] Ω) → ZMod (p ^ M))
    (he : ∀ g, g (zt ε p M) = zt ε p M ^ (e g).val) (s t : Ω ≃ₐ[ℚ] Ω) : e (s * t) = e s * e t := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hζ := IsNTr.isPrimitiveRoot_zt ε p M
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← he, AlgEquiv.mul_apply, he t, map_pow, he s, GlobalTheory.K4.TopW.pow_val_mul hζ, ← pow_mul, ← pow_mul, mul_comm]

theorem lc_one (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (M : ℕ) (hM : 1 ≤ M) (e : (Ω ≃ₐ[ℚ] Ω) → ZMod (p ^ M))
    (he : ∀ g, g (zt ε p M) = zt ε p M ^ (e g).val) : e 1 = 1 := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  haveI : Fact (1 < p ^ M) := ⟨Nat.one_lt_pow (by omega) hpp.one_lt⟩
  have hζ := IsNTr.isPrimitiveRoot_zt ε p M
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← he, AlgEquiv.one_apply, ZMod.val_one, pow_one]

theorem fix_iff (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (L m : ℕ) (hmL : m ≤ L) (g : Ω ≃ₐ[ℚ] Ω) (t : ZMod (p ^ L))
    (hg : g (zt ε p L) = zt ε p L ^ t.val) : g (zt ε p m) = zt ε p m ↔ t.val ≡ 1 [MOD p ^ m] := by
  have hζm := IsNTr.isPrimitiveRoot_zt ε p m
  have hz : zt ε p L ^ p ^ (L - m) = zt ε p m := by
    have := IsNTr.zt_pow ε p m (L - m); rwa [Nat.add_sub_cancel' hmL] at this
  have e : g (zt ε p m) = zt ε p m ^ t.val := by
    rw [← hz, map_pow, hg, ← pow_mul, ← pow_mul, mul_comm]
  have hpos : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
  have h1 : ∀ a, zt ε p m ^ a = zt ε p m ^ (a % p ^ m) := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a (p ^ m), pow_add, pow_mul, hζm.pow_eq_one, one_pow, mul_one]
  rw [e]
  nth_rewrite 2 [← pow_one (zt ε p m)]
  rw [h1 t.val, h1 1]
  exact ⟨fun h => hζm.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) h, fun h => by rw [show t.val % p ^ m = 1 % p ^ m from h]⟩

end Lev

theorem pows_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm : 1 ≤ m) (hmL : m ≤ L) (u : (ZMod (p ^ L))ˣ)
    (hu : (u : ZMod (p ^ L)) = 1 + (p : ZMod (p ^ L)) ^ m) :
    orderOf u = p ^ (L - m) ∧ (Finset.range (p ^ (L - m))).image (fun k => u ^ k) =
      Finset.univ.filter (fun x : (ZMod (p ^ L))ˣ => (x : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]) := by
  have hpp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  have hord : orderOf u = p ^ (L - m) := by
    rw [← orderOf_units, hu]
    have h := ZMod.orderOf_one_add_mul_prime_pow hpp m (by omega) (by nlinarith) 1
      (by exact_mod_cast hpp.not_dvd_one) (L - m)
    rw [Nat.sub_add_cancel hmL, Int.cast_one, mul_one] at h
    exact h
  refine ⟨hord, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hd : p ^ m ∣ p ^ L := pow_dvd_pow p hmL
    have h1 : (((u ^ k : (ZMod (p ^ L))ˣ) : ZMod (p ^ L)).val : ZMod (p ^ m)) = ((1 : ℕ) : ZMod (p ^ m)) := by
      rw [← ZMod.cast_eq_val, ← ZMod.castHom_apply (h := hd), Units.val_pow_eq_pow_val, map_pow, hu, map_add, map_one,
        map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, add_zero, one_pow, Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  · rw [Finset.card_image_of_injOn, Finset.card_range, IsNTr.card_filter p L m hm hmL]
    intro a ha b hb hab
    have := (pow_inj_mod (x := u)).1 hab
    rwa [hord, Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)] at this

theorem sum_shift {M : Type*} [AddCommMonoid M] (N j : ℕ) (hj : j < N) (f : ℕ → M) :
    ∑ k ∈ Finset.range N, f ((k + N - j) % N) = ∑ k ∈ Finset.range N, f k := by
  have key1 : ∀ k < N, (k + N - j) % N = if j ≤ k then k - j else k + N - j := fun k hk => by
    split_ifs with h
    · rw [show k + N - j = (k - j) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  have key2 : ∀ k < N, (k + j) % N = if k + j < N then k + j else k + j - N := fun k hk => by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · conv_lhs => rw [show k + j = (k + j - N) + N by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  apply Finset.sum_nbij' (fun k => (k + N - j) % N) (fun k => (k + j) % N)
  · intro k _; simpa using Nat.mod_lt _ (show 0 < N by omega)
  · intro k _; simpa using Nat.mod_lt _ (show 0 < N by omega)
  · intro k hk
    replace hk : k < N := by simpa using hk
    rw [key1 k hk]
    split_ifs with h
    · rw [key2 _ (by omega)]; split_ifs <;> omega
    · rw [key2 _ (by omega)]; split_ifs <;> omega
  · intro k hk
    replace hk : k < N := by simpa using hk
    rw [key2 k hk]
    split_ifs with h
    · rw [key1 _ (by omega)]; split_ifs <;> omega
    · rw [key1 _ (by omega)]; split_ifs <;> omega
  · intro k _; rfl

section Tt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

def Tt (ε : Ω →+* ℂ) (p L n : ℕ) (g : Ω ≃ₐ[ℚ] Ω) (t : ZMod (p ^ n)) : Prop :=
  g (zt ε p (L + n)) = zt ε p n ^ t.val * zt ε p (L + n)

variable {ε : Ω →+* ℂ} {p : ℕ} [Fact p.Prime] {L n : ℕ}

theorem fix_le {a b : ℕ} (h : a ≤ b) {g : Ω ≃ₐ[ℚ] Ω} (hg : g (zt ε p b) = zt ε p b) : g (zt ε p a) = zt ε p a := by
  have hz := IsNTr.zt_pow ε p a (b - a)
  rw [Nat.add_sub_cancel' h] at hz
  rw [← hz, map_pow, hg]

omit [IsAlgClosure ℚ Ω] in
theorem fix_pow {x : Ω} {g : Ω ≃ₐ[ℚ] Ω} (hg : g x = x) (k : ℕ) : (g ^ k) x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hg, ih]

theorem tt_exists {g : Ω ≃ₐ[ℚ] Ω} (hg : g (zt ε p L) = zt ε p L) : ∃ t, Tt ε p L n g t := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hζ := IsNTr.isPrimitiveRoot_zt ε p (L + n)
  have h0 : zt ε p (L + n) ≠ 0 := hζ.ne_zero (pow_ne_zero _ hpp.ne_zero)
  have h1 : (g (zt ε p (L + n)) / zt ε p (L + n)) ^ p ^ n = 1 := by
    rw [div_pow, ← map_pow, IsNTr.zt_pow, hg,
      div_self ((IsNTr.isPrimitiveRoot_zt ε p L).ne_zero (pow_ne_zero _ hpp.ne_zero))]
  obtain ⟨i, hi, he⟩ := (IsNTr.isPrimitiveRoot_zt ε p n).eq_pow_of_pow_eq_one h1
  exact ⟨i, by rw [Tt, ZMod.val_natCast_of_lt hi, he, div_mul_cancel₀ _ h0]⟩

theorem tt_mul {g h : Ω ≃ₐ[ℚ] Ω} {t t' : ZMod (p ^ n)} (hg : g (zt ε p n) = zt ε p n) (h1 : Tt ε p L n g t)
    (h2 : Tt ε p L n h t') : Tt ε p L n (g * h) (t + t') := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold Tt at *
  rw [AlgEquiv.mul_apply, h2, map_mul, map_pow, hg, h1, GlobalTheory.K4.TopW.pow_val_add (IsNTr.isPrimitiveRoot_zt ε p n)]
  ring

theorem tt_pow {g : Ω ≃ₐ[ℚ] Ω} {t : ZMod (p ^ n)} (hg : g (zt ε p n) = zt ε p n) (h1 : Tt ε p L n g t) (k : ℕ) :
    Tt ε p L n (g ^ k) ((k : ZMod (p ^ n)) * t) := by
  induction k with
  | zero => simp [Tt]
  | succ k ih =>
    have := tt_mul (fix_pow hg k) ih h1
    rwa [pow_succ, Nat.cast_succ, add_mul, one_mul]

theorem tt_transfer (hL : 1 ≤ L) (hnL : n ≤ L) (g s : Ω ≃ₐ[ℚ] Ω) (N j : ℕ) (ta tb : ZMod (p ^ n))
    (ha : ((g ^ j)⁻¹ * s) (zt ε p L) = zt ε p L) (hb : (g ^ N) (zt ε p L) = zt ε p L)
    (hta : Tt ε p L n ((g ^ j)⁻¹ * s) ta) (htb : Tt ε p L n (g ^ N) tb) :
    (∀ k k', k' + j = k → Tt ε p L n ((g ^ k)⁻¹ * s * g ^ k') ta) ∧
    (∀ k k', k' + j = k + N → Tt ε p L n ((g ^ k)⁻¹ * s * g ^ k') (ta + tb)) ∧
    Tt ε p L n (s ^ N) (N * ta + j * tb) := by
  obtain ⟨e, he⟩ := lc_exists ε p (L + n)
  let E : (Ω ≃ₐ[ℚ] Ω) →* ZMod (p ^ (L + n)) :=
    { toFun := e, map_one' := lc_one ε p _ (by omega) e he, map_mul' := lc_mul ε p _ e he }
  have tr : ∀ (x y : Ω ≃ₐ[ℚ] Ω) t, E.toHomUnits x = E.toHomUnits y → Tt ε p L n y t → Tt ε p L n x t := by
    intro x y t hxy h
    have : e x = e y := congrArg Units.val hxy
    unfold Tt at *
    rw [← h, he x, he y, this]
  generalize E.toHomUnits = φ at tr
  have ha' := fix_le hnL ha
  refine ⟨fun k k' hk => tr _ _ _ ?_ hta, fun k k' hk => tr _ _ _ ?_ (tt_mul ha' hta htb),
    tr _ _ _ ?_ (tt_mul (fix_pow ha' N) (tt_pow ha' hta N) (tt_pow (fix_le hnL hb) htb j))⟩
  · subst hk
    simp only [map_mul, map_inv, map_pow, pow_add, mul_inv]
    generalize φ g ^ k' = x
    rw [mul_right_comm, mul_right_comm x⁻¹, inv_mul_cancel, one_mul]
  · simp only [map_mul, map_inv, map_pow]
    have h : φ g ^ k' * φ g ^ j = φ g ^ k * φ g ^ N := by rw [← pow_add, ← pow_add, hk]
    rw [mul_right_comm, mul_right_comm (φ g ^ j)⁻¹]
    congr 1
    rw [inv_mul_eq_iff_eq_mul, mul_left_comm, eq_inv_mul_iff_mul_eq, mul_comm, h]
  · simp only [map_mul, map_inv, map_pow, mul_pow, inv_pow, ← pow_mul]
    rw [mul_comm N j, mul_right_comm, inv_mul_cancel, one_mul]

end Tt

section Alg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {l n : ℕ}

theorem abel_sum [NeZero (l ^ n)] (N j : ℕ) (hj : j ≤ N) (a : Ω) (ha : a ∈ A) (f : ℕ → Ω) (hf : ∀ k, f k ∈ A) (hN : f N = f 0)
    (ta tb : ZMod (l ^ n)) :
    CgA A l n (∑ k ∈ Finset.range N, (a + (f (k + 1) - f k)) * (((if k < j then ta + tb else ta).val : ℕ) : Ω))
      ((f j - f 0) * (tb.val : Ω) + a * ((((N : ZMod (l ^ n)) * ta + j * tb).val : ℕ) : Ω)) := by
  have h1 : CgA A l n (∑ k ∈ Finset.range N, (a + (f (k + 1) - f k)) * (((if k < j then ta + tb else ta).val : ℕ) : Ω))
      (∑ k ∈ Finset.range N, (a + (f (k + 1) - f k)) * ((ta.val : Ω) + if k < j then (tb.val : Ω) else 0)) := by
    refine cg_sum _ _ _ fun k _ => cg_mul _ (add_mem ha (sub_mem (hf _) (hf _))) ?_
    split_ifs with h
    · rw [← Nat.cast_add]; exact cg_nat (by simp)
    · rw [add_zero]; exact cg_refl _
  have h2 : ∑ k ∈ Finset.range N, (a + (f (k + 1) - f k)) * ((ta.val : Ω) + if k < j then (tb.val : Ω) else 0) =
      (f j - f 0) * (tb.val : Ω) + a * ((N * ta.val + j * tb.val : ℕ) : Ω) := by
    have hfil : (Finset.range N).filter (fun k => k < j) = Finset.range j := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
    simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]
    rw [← Finset.sum_filter, hfil, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_range_sub, Finset.sum_range_sub, hN]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  rw [h2] at h1
  exact cg_trans h1 (cg_add (cg_refl _) (cg_mul _ ha (cg_nat (by simp))))

theorem shapiro {G : Type} [CommGroup G] (χ : (Ω ≃ₐ[ℚ] Ω) →* G) (z : (Ω ≃ₐ[ℚ] Ω) → G → Ω)
    (hz : ∀ s t, Stab A s → Stab A t → ∀ x, CgA A l n (z (s * t) x) (z s x + s (z t (x * (χ s)⁻¹))))
    (g s : Ω ≃ₐ[ℚ] Ω) (hg : Stab A g) (hs : Stab A s) (N j : ℕ) (hj : j < N) (ξ : Ω) (w : ℕ → Ω)
    (hx : ∀ k < N, χ g ^ k * (χ s)⁻¹ = χ g ^ ((k + N - j) % N))
    (h1 : ∀ k < N, CgA A l n (z ((g ^ k)⁻¹ * s * g ^ ((k + N - j) % N)) 1)
      (((g ^ k)⁻¹ * s * g ^ ((k + N - j) % N)) ξ - ξ + w k)) :
    CgA A l n (∑ k ∈ Finset.range N, z s (χ g ^ k))
      (s (∑ k ∈ Finset.range N, ((g ^ k) ξ - z (g ^ k) (χ g ^ k))) - (∑ k ∈ Finset.range N, ((g ^ k) ξ - z (g ^ k) (χ g ^ k))) +
        ∑ k ∈ Finset.range N, (g ^ k) (w k)) := by
  nth_rewrite 1 [← sum_shift N j hj (fun k => (g ^ k) ξ - z (g ^ k) (χ g ^ k))]
  rw [map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine cg_sum _ _ _ fun k hk => ?_
  replace hk := Finset.mem_range.1 hk
  have a1 := hz s _ hs (stab_pow hg ((k + N - j) % N)) (χ g ^ k)
  have a2 := hz _ _ (stab_pow hg k) (stab_mul (stab_mul (stab_inv (stab_pow hg k)) hs) (stab_pow hg ((k + N - j) % N))) (χ g ^ k)
  have a3 := cg_map (stab_pow hg k) (h1 k hk)
  have e : g ^ k * ((g ^ k)⁻¹ * s * g ^ ((k + N - j) % N)) = s * g ^ ((k + N - j) % N) := by group
  rw [map_add, map_sub, ← AlgEquiv.mul_apply (g ^ k) (_ * _), e, AlgEquiv.mul_apply] at a3
  rw [e, map_pow, mul_inv_cancel] at a2
  rw [hx k hk] at a1
  have a4 := cg_sub (cg_trans (cg_symm a1) (cg_trans a2 (cg_add (cg_refl _) a3)))
    (cg_refl (s (z (g ^ ((k + N - j) % N)) (χ g ^ ((k + N - j) % N)))))
  refine cg_congr a4 (by ring) ?_
  rw [map_sub]; ring

end Alg

section Inert

open ReciprocityTheory.Gal Pointwise

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem mem_ine_iff {A : ValuationSubring Ω} {s : Ω ≃ₐ[ℚ] Ω} :
    s ∈ Ine (F := ℚ) A ↔ Stab A s ∧ ∀ x ∈ A, A.valuation (s x - x) < 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨apply_mem_iff_of_mem_Dec h1, fun x hx => h2 x ((A.valuation_le_one_iff x).2 hx)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun x hx => h2 x ((A.valuation_le_one_iff x).1 hx)⟩
    show s • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    exact stab_inv h1 x

theorem exists_ine_pow [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω)
    (hp : ((p : ℕ) : Ω) ∈ A.nonunits) (L : ℕ) (u : (ZMod (p ^ L))ˣ) :
    ∃ s ∈ Ine (F := ℚ) A, s (zt ε p L) = zt ε p L ^ (u : ZMod (p ^ L)).val := by
  obtain ⟨⟨s, hs⟩, h⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective p Ω A (A.mem_nonunits_iff.1 hp) L u
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  refine ⟨s, hs, ?_⟩
  rw [← h]
  exact cyclotomicCharacter.spec (L := Ω) p (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G ℚ Ω) Ω s) _
    (IsNTr.isPrimitiveRoot_zt ε p L).pow_eq_one

end Inert

theorem cores_law : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits →
  ∀ (L n m : ℕ), 1 ≤ m → m ≤ n → n ≤ L → ∀ χ : (Ω ≃ₐ[ℚ] Ω) → (ZMod (p ^ L))ˣ, (∀ s, s (zt ε p L) = zt ε p L ^ (χ s : ZMod (p ^ L)).val) →
  ∀ z : (Ω ≃ₐ[ℚ] Ω) → (ZMod (p ^ L))ˣ → ℚ → Ω, (∀ s x r, z s x r ∈ A) →
  (∀ s t, Stab A s → Stab A t → ∀ x r, CgA A p n (z (s * t) x r) (z s x r + s (z t (x * (χ s)⁻¹) r))) →
  ∀ ξ F : ℚ → Ω, (∀ r, ξ r ∈ A ∧ InZl ε p L (F r)) →
  (∀ s, Stab A s → (∀ x ∈ A, A.valuation (s x - x) < 1) → χ s = 1 → ∀ tt : ZMod (p ^ n), s (zt ε p (L + n)) = zt ε p n ^ tt.val * zt ε p (L + n) →
    ∀ r, CgA A p n (z s 1 r) (s (ξ r) - ξ r + F r * (tt.val : Ω))) →
  ∀ F' : ℚ → Ω, (∀ r, IsNT ε p L m (F r) (F' r)) →
  ∃ ξ' : ℚ → Ω, (∀ r, ξ' r ∈ A) ∧ ∀ s, Stab A s → (∀ x ∈ A, A.valuation (s x - x) < 1) → s (zt ε p m) = zt ε p m → ∀ tt : ZMod (p ^ n), IsLamG ε p n m s tt →
    ∀ r, CgA A p n ((p : Ω) ^ c * ∑ x ∈ Finset.univ.filter (fun x : (ZMod (p ^ L))ˣ => (x : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), z s x r)
      (s (ξ' r) - ξ' r + (p : Ω) ^ c * (F' r * (tt.val : Ω))) := by
  intro p _ hp2
  obtain ⟨c, hc⟩ := GlobalTheory.TateInv.tate_inv p hp2
  refine ⟨c, ?_⟩
  intro Ω _ _ _ ε A hpA L n m hm hmn hnL χ₀ hχ₀ z hzA hcoc ξ F hξF hz1 F' hF'
  have hpp : p.Prime := Fact.out
  have hmL : m ≤ L := hmn.trans hnL
  haveI : NeZero (p ^ L) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  haveI : Fact (1 < p ^ L) := ⟨Nat.one_lt_pow (by omega) hpp.one_lt⟩
  have hζL := IsNTr.isPrimitiveRoot_zt ε p L
  let χ : (Ω ≃ₐ[ℚ] Ω) →* (ZMod (p ^ L))ˣ := MonoidHom.mk' χ₀ fun s t =>
    Units.ext (lc_mul ε p L (fun g => (χ₀ g : ZMod (p ^ L))) hχ₀ s t)
  have hχ : ∀ s, s (zt ε p L) = zt ε p L ^ (χ s : ZMod (p ^ L)).val := hχ₀
  have fixL : ∀ g, χ g = 1 → g (zt ε p L) = zt ε p L := fun g h => by
    rw [hχ, h, Units.val_one, ZMod.val_one, pow_one]
  have hcop : Nat.Coprime (1 + p ^ m) (p ^ L) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp]
    intro h
    exact hpp.not_dvd_one ((Nat.dvd_add_left (dvd_pow_self p (by omega))).1 h)
  obtain ⟨g, hgI, hg⟩ := exists_ine_pow ε p A hpA L (ZMod.unitOfCoprime (1 + p ^ m) hcop)
  have hgA : Stab A g := (mem_ine_iff.1 hgI).1
  have hχg : χ g = ZMod.unitOfCoprime (1 + p ^ m) hcop :=
    Units.ext (ZMod.val_injective _ (hζL.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [← hχ, hg])))
  have hgL : g (zt ε p L) = zt ε p L ^ (1 + p ^ m) := by
    rw [hg, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div (1 + p ^ m) (p ^ L), pow_add, pow_mul, hζL.pow_eq_one, one_pow, mul_one]
  obtain ⟨hord, himg⟩ := pows_eq p hp2 L m hm hmL (χ g) (by rw [hχg, ZMod.coe_unitOfCoprime]; push_cast; rfl)
  have hgm : g (zt ε p m) = zt ε p m := by
    have hz := IsNTr.zt_pow ε p m (L - m)
    rw [Nat.add_sub_cancel' hmL] at hz
    rw [← hz, map_pow, hgL, ← pow_mul, add_mul, one_mul, ← pow_add, Nat.add_sub_cancel' hmL, pow_add, hζL.pow_eq_one, mul_one]
  have hlam := fun s hs tt tt' => GlobalTheory.LamEq.lam_eq ε p hp2 L n m hm hmn hnL s hs tt tt'
  generalize hN : p ^ (L - m) = N at hord himg hlam
  have huN : χ g ^ N = 1 := by rw [← hord, pow_orderOf_eq_one]
  have hb : (g ^ N) (zt ε p L) = zt ε p L := fixL _ (by rw [map_pow, huN])
  obtain ⟨tb, htb⟩ := tt_exists (n := n) hb
  choose H hHZ hH using fun r => hc ε L m hm hmL (F r) (F' r) (hξF r).2 (hF' r) g hgL
  have hHA : ∀ r, H r ∈ A := fun r => mem_of_inZl ε p A hpA L _ (hHZ r)
  have hF'Z : ∀ r, InZl ε p m (F' r) := fun r => by
    obtain ⟨F'', -, h1, h2⟩ := GlobalTheory.NTr.normTrace_exists_unique ε p L m hm hmL (F r) (hξF r).2
    rw [h2 _ (hF' r)]; exact h1
  have hpc : (p : Ω) ^ c ∈ A := pow_mem (nat_mem p) c
  refine ⟨fun r => (p : Ω) ^ c * (∑ k ∈ Finset.range N, ((g ^ k) (ξ r) - z (g ^ k) (χ g ^ k) r)) + H r * (tb.val : Ω),
    fun r => add_mem (mul_mem hpc (sum_mem fun k _ => sub_mem ((stab_pow hgA k _).2 (hξF r).1) (hzA _ _ _)))
      (mul_mem (hHA r) (nat_mem _)), fun s hsA hsI hsm tt htt r => ?_⟩
  obtain ⟨j, hjN, hj⟩ : ∃ j < N, χ g ^ j = χ s := by
    have h : χ s ∈ (Finset.range N).image (fun k => χ g ^ k) := by
      rw [himg, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (fix_iff ε p L m hmL s _ (hχ s)).1 hsm⟩
    simpa using h
  have ha : ((g ^ j)⁻¹ * s) (zt ε p L) = zt ε p L := fixL _ (by rw [map_mul, map_inv, map_pow, hj, inv_mul_cancel])
  obtain ⟨ta, hta⟩ := tt_exists (n := n) ha
  obtain ⟨t1, t2, t3⟩ := tt_transfer (by omega) hnL g s N j ta tb ha hb hta htb
  have hkp : ∀ k < N, (k + N - j) % N + j = if k < j then k + N else k := fun k hk => by
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [show k + N - j = (k - j) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  have hx : ∀ k < N, χ g ^ k * (χ s)⁻¹ = χ g ^ ((k + N - j) % N) := fun k hk => by
    rw [mul_inv_eq_iff_eq_mul, ← hj, ← pow_add, hkp k hk]
    split_ifs
    · rw [pow_add, huN, mul_one]
    · rfl
  have key := shapiro (A := A) (l := p) (n := n) χ (fun s x => z s x r) (fun s t hs ht x => hcoc s t hs ht x r) g s hgA hsA N j hjN (ξ r)
    (fun k => F r * (((if k < j then ta + tb else ta).val : ℕ) : Ω)) hx (fun k hk => by
      have hI := mem_ine_iff.1 (mul_mem (mul_mem (inv_mem (pow_mem hgI k)) (mem_ine_iff.2 ⟨hsA, hsI⟩))
        (pow_mem hgI ((k + N - j) % N)))
      refine hz1 _ hI.1 hI.2 ?_ _ ?_ r
      · show χ _ = 1
        rw [map_mul, map_mul, map_inv, map_pow, map_pow, ← hx k hk, mul_comm (χ g ^ k), mul_assoc, mul_inv_cancel_left,
          inv_mul_cancel]
      · have h := hkp k hk
        split_ifs at h ⊢
        · exact t2 _ _ h
        · exact t1 _ _ h)
  have hsum : ∑ x ∈ Finset.univ.filter (fun x : (ZMod (p ^ L))ˣ => (x : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), z s x r =
      ∑ k ∈ Finset.range N, z s (χ g ^ k) r := by
    rw [← himg, Finset.sum_image]
    intro a ha b hb hab
    have := (pow_inj_mod (x := χ g)).1 hab
    rwa [hord, Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)] at this
  have hab := abel_sum (A := A) (l := p) (n := n) N j hjN.le ((p : Ω) ^ c * F' r)
    (mul_mem hpc (mem_of_inZl ε p A hpA m _ (hF'Z r))) (fun k => (g ^ k) (H r)) (fun k => (stab_pow hgA k _).2 (hHA r))
    (IsNTr.apply_eq_of_mem_adjoin (hHZ r).mem_adjoin (by rw [hb, pow_zero, AlgEquiv.one_apply])) ta tb
  have hjs : (g ^ j) (H r) = s (H r) :=
    IsNTr.apply_eq_of_mem_adjoin (hHZ r).mem_adjoin (by rw [hχ (g ^ j), hχ s, map_pow, hj])
  rw [← hlam s hsm tt _ htt t3, hjs, pow_zero, AlgEquiv.one_apply] at hab
  have hterm : (p : Ω) ^ c * ∑ k ∈ Finset.range N, (g ^ k) (F r * (((if k < j then ta + tb else ta).val : ℕ) : Ω)) =
      ∑ k ∈ Finset.range N, ((p : Ω) ^ c * F' r + ((g ^ (k + 1)) (H r) - (g ^ k) (H r))) *
        (((if k < j then ta + tb else ta).val : ℕ) : Ω) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := congrArg (g ^ k) (hH r)
    have h2 : (g ^ k) (F' r) = (1 : Ω ≃ₐ[ℚ] Ω) (F' r) :=
      IsNTr.apply_eq_of_mem_adjoin (hF'Z r).mem_adjoin (by rw [fix_pow hgm, AlgEquiv.one_apply])
    rw [map_mul, map_pow, map_natCast, map_sub, map_sub, h2, AlgEquiv.one_apply, ← AlgEquiv.mul_apply, ← pow_succ] at h1
    rw [map_mul, map_natCast, ← h1]; ring
  rw [hsum]
  have k2 := cg_mul _ hpc key
  rw [mul_add, hterm] at k2
  refine cg_congr (cg_trans k2 (cg_add (cg_refl _) hab)) rfl ?_
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.Glue.CorShap
