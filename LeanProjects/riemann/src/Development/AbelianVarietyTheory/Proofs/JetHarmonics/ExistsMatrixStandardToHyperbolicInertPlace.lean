import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.InertHyperbolic

theorem exists_norm_eq_neg_one (K : Type) [Field K] (l : ℕ) (hl : l.Prime) (h2 : l ≠ 2) [CharP K l]
    (t : K) (ht : t ≠ 0) (htl : t ^ l = -t) : ∃ a b : ℤ, (a : K) ^ 2 - (b : K) ^ 2 * t ^ 2 = -1 := by
  haveI : Fact l.Prime := ⟨hl⟩
  have hd : (t ^ 2) ^ l = t ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, htl]; ring
  have hmem : t ^ 2 ∈ (⊥ : Subfield K) := (Subfield.mem_bot_iff_pow_eq_self K l).2 hd
  obtain ⟨d, hdd⟩ := (mem_bot_iff_intCast l K).1 hmem
  have hd0 : (d : ZMod l) ≠ 0 := by
    intro h
    have := congrArg (ZMod.castHom (dvd_refl l) K) h
    rw [map_intCast, map_zero, hdd] at this
    exact ht (pow_eq_zero_iff (two_ne_zero) |>.1 this)
  have hodd : Fintype.card (ZMod l) % 2 = 1 := by
    rw [ZMod.card]; exact Nat.odd_iff.1 (hl.odd_of_ne_two h2)
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := ZMod l)
    (f := Polynomial.X ^ 2 + Polynomial.C 1) (g := Polynomial.C (-(d : ZMod l)) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_add_C (by norm_num) 1)
    (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 hd0)) hodd
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective b
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at hab
  have := congrArg (ZMod.castHom (dvd_refl l) K) hab
  simp only [map_add, map_mul, map_pow, map_neg, map_one, map_intCast, map_zero] at this
  rw [hdd] at this
  linear_combination this

variable {C : Type} [Field C] {V : VF C}

theorem mm_iff {x : C} : V.MM x ↔ ∃ c : ℝ, 0 < c ∧ V.Ge c x := by
  unfold VF.MM VF.Ge
  induction V.v x using WithTop.recTopCoe with
  | top => exact ⟨fun _ => ⟨1, one_pos, le_top⟩, fun _ => by simp⟩
  | coe t =>
    constructor
    · intro h
      exact ⟨t, by exact_mod_cast h, le_rfl⟩
    · rintro ⟨c, hc, h⟩
      have : c ≤ t := by exact_mod_cast h
      exact_mod_cast hc.trans_le this

theorem mm_or {x y : C} (h : V.MM (x * y)) : V.MM x ∨ V.MM y := by
  unfold VF.MM at *
  by_contra hn
  push Not at hn
  rw [V.v.map_mul] at h
  exact absurd h (not_lt.2 (add_nonpos hn.1 hn.2))

theorem not_mm_one : ¬ V.MM (1 : C) := by simp [VF.MM]

def maxId (V : VF C) : Ideal V.RR where
  carrier := {x | V.MM (x : C)}
  add_mem' := by
    intro a b ha hb
    exact V.v.map_lt_add ha hb
  zero_mem' := by simp [VF.MM]
  smul_mem' := by
    intro c x hx
    obtain ⟨e, he, h⟩ := mm_iff.1 hx
    exact mm_iff.2 ⟨e, he, VF.Ge.mul_int c.2 h⟩

theorem maxId_prime (V : VF C) : (maxId V).IsPrime :=
  ⟨fun h => not_mm_one (V := V) ((Ideal.eq_top_iff_one _).1 h), fun h => mm_or h⟩

theorem exists_residue (V : VF C) :
    ∃ (K : Type) (_ : Field K) (φ : V.RR →+* K), ∀ x, φ x = 0 ↔ V.MM (x : C) := by
  haveI := maxId_prime V
  refine ⟨FractionRing (V.RR ⧸ maxId V), inferInstance,
    (algebraMap (V.RR ⧸ maxId V) _).comp (Ideal.Quotient.mk _), fun x => ?_⟩
  rw [RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem mm_l : V.MM (V.l : C) := mm_iff.2 ⟨1, one_pos, VF.ge_l⟩

theorem exists_norm_congr (h2 : V.l ≠ 2) (t : C) (ht : V.v t = 0) (htl : V.MM (t ^ V.l + t)) :
    ∃ a b : ℤ, V.MM ((a : C) ^ 2 - (b : C) ^ 2 * t ^ 2 + 1) := by
  obtain ⟨K, _, φ, hφ⟩ := exists_residue V
  haveI : Fact V.l.Prime := ⟨V.l_prime⟩
  haveI : CharP K V.l := by
    rw [CharP.charP_iff_prime_eq_zero V.l_prime, ← map_natCast φ, hφ]
    simpa using mm_l
  let T : V.RR := ⟨t, by show V.Ge 0 t; simp [VF.Ge, ht]⟩
  have h1 : φ T ≠ 0 := by
    rw [Ne, hφ]; simp [T, VF.MM, ht]
  have h3 : φ T ^ V.l = -φ T := by
    rw [← add_eq_zero_iff_eq_neg, ← map_pow, ← map_add, hφ]
    simpa [T] using htl
  obtain ⟨a, b, hab⟩ := exists_norm_eq_neg_one K V.l V.l_prime h2 (φ T) h1 h3
  refine ⟨a, b, ?_⟩
  have : φ ((a : V.RR) ^ 2 - (b : V.RR) ^ 2 * T ^ 2 + 1) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_one, hab]; ring
  rw [hφ] at this
  simpa [T] using this

theorem ge_pow_sub_one {s : C} {w : ℝ} (hw : 0 ≤ w) (h : V.Ge w (s - 1)) (i : ℕ) : V.Ge w (s ^ i - 1) := by
  have hs : V.Ge 0 s := by simpa using (h.mono hw).add VF.Ge.one
  rw [← geom_sum_mul]
  exact VF.Ge.mul_int (VF.Ge.sum fun j _ => hs.pow j) h

theorem ge_pow_l_pow {s : C} {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (h : V.Ge c (s - 1)) (k : ℕ) :
    V.Ge ((k + 1) * c) (s ^ V.l ^ k - 1) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, pow_mul, ← geom_sum_mul]
    have h1 : V.Ge c (∑ i ∈ Finset.range V.l, (s ^ V.l ^ k) ^ i) := by
      have : ∑ i ∈ Finset.range V.l, (s ^ V.l ^ k) ^ i
          = (V.l : C) + ∑ i ∈ Finset.range V.l, ((s ^ V.l ^ k) ^ i - 1) := by
        simp [Finset.sum_sub_distrib]
      rw [this]
      refine (VF.ge_l.mono hc1).add (VF.Ge.sum fun i _ => ?_)
      rw [← pow_mul]; exact ge_pow_sub_one hc.le h _
    refine (h1.mul ih).mono (le_of_eq ?_)
    push_cast; ring

theorem exists_odd_pow (h2 : V.l ≠ 2) {s : C} (h : V.MM (s - 1)) (N : ℕ) :
    ∃ m : ℕ, V.Ge N (s ^ (2 * m + 1) - 1) := by
  obtain ⟨e, he, h⟩ := mm_iff.1 h
  have hc : 0 < min e 1 := lt_min he one_pos
  obtain ⟨k, hk⟩ := exists_nat_ge ((N : ℝ) / min e 1)
  obtain ⟨m, hm⟩ := (V.l_prime.odd_of_ne_two h2).pow (n := k)
  refine ⟨m, ?_⟩
  rw [← hm]
  refine (ge_pow_l_pow hc (min_le_right _ _) (h.mono (min_le_left _ _)) k).mono ?_
  rw [div_le_iff₀ hc] at hk
  nlinarith

theorem ge_inv {s : C} (hs : ¬ V.MM s) : V.Ge 0 s⁻¹ := by
  unfold VF.MM at hs
  unfold VF.Ge
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have h : V.v s + V.v s⁻¹ = 0 := by rw [← V.v.map_mul, mul_inv_cancel₀ hs0, V.v.map_one]
  have : V.v s + V.v s⁻¹ ≤ 0 + V.v s⁻¹ := by gcongr; exact not_lt.1 hs
  rw [h, zero_add] at this
  exact this

theorem ge_half (h2 : V.l ≠ 2) : V.Ge 0 (2 : C)⁻¹ := by
  refine ge_inv fun h => not_mm_one (V := V) ?_
  obtain ⟨m, hm⟩ := V.l_prime.odd_of_ne_two h2
  obtain ⟨e, he, h⟩ := mm_iff.1 h
  have : (1 : C) = V.l - m * 2 := by rw [hm]; push_cast; ring
  rw [this]
  exact mm_iff.2 ⟨min e 1, lt_min he one_pos, (VF.ge_l.mono (min_le_right _ _)).sub
    ((VF.Ge.mul_int (VF.ge_natCast m) h).mono (min_le_left _ _))⟩

theorem exists_half [CharZero C] (h2 : V.l ≠ 2) (N : ℕ) : ∃ m : ℕ, V.Ge N ((2 : C)⁻¹ - m) := by
  obtain ⟨m, hm⟩ := (V.l_prime.odd_of_ne_two h2).pow (n := N)
  refine ⟨m + 1, ?_⟩
  have hp : V.Ge N ((V.l : C) ^ N) := by
    clear hm
    induction N with
    | zero => simpa using VF.Ge.one
    | succ n ih => rw [pow_succ]; push_cast; exact ih.mul VF.ge_l
  have : (2 : C)⁻¹ - (m + 1 : ℕ) = -(2⁻¹ * (V.l : C) ^ N) := by
    rw [← Nat.cast_pow, hm]; push_cast; ring
  rw [this]
  exact (VF.Ge.mul_int (ge_half h2) hp).neg

theorem exists_pair [IsAlgClosed C] (h2 : V.l ≠ 2) (O : Type) [CommRing O] [StarRing O]
    (em : ZMod 2 → (O →+* C)) (hint : ∀ a x, V.Ge 0 (em a x))
    (hfr : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) (hsep : ∃ x, V.v (em 0 x - em 1 x) = 0)
    (hst : ∀ a x, em a (star x) = em (a + 1) x) :
    ∃ z : ZMod 2 → C, (∀ a, z (a + 1) * z a = -1) ∧ (∀ a, V.Ge 0 (z a)) ∧
      ∀ N : ℕ, ∃ y : O, ∀ a, V.Ge N (z a - em a y) := by
  obtain ⟨x, hx⟩ := hsep
  have e11 : (1 : ZMod 2) + 1 = 0 := rfl
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  set t := em 0 x - em 1 x with htdef
  have d0 : em 0 (x - star x) = t := by rw [map_sub, hst, zero_add]
  have d1 : em 1 (x - star x) = -t := by rw [map_sub, hst, e11, htdef]; ring
  have htl : V.MM (t ^ V.l + t) := by
    have := hfr 0 (x - star x)
    rw [zero_add, d0, d1] at this
    unfold VF.MM at this ⊢
    rw [← V.v.map_neg]
    convert this using 2; ring
  obtain ⟨a, b, hab⟩ := exists_norm_congr h2 t hx htl
  set w : O := a + b * (x - star x) with hw
  have w0 : em 0 w = a + b * t := by rw [hw, map_add, map_mul, d0]; simp
  have w1 : em 1 w = a - b * t := by rw [hw, map_add, map_mul, d1]; simp [sub_eq_add_neg]
  set u : C := -((a : C) ^ 2 - (b : C) ^ 2 * t ^ 2) with hu
  have hwu : ∀ c, em (c + 1) w * em c w = -u := by
    intro c
    rcases hcases c with rfl | rfl
    · rw [zero_add, w0, w1, hu]; ring
    · rw [e11, w0, w1, hu]; ring
  obtain ⟨s, hsu, hs1⟩ : ∃ s : C, s ^ 2 = u ∧ V.MM (s - 1) := by
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq u (n := 2) two_pos
    have : V.MM ((s - 1) * (-s - 1)) := by
      convert hab using 1
      linear_combination -hs - hu
    rcases mm_or this with h | h
    · exact ⟨s, hs, h⟩
    · exact ⟨-s, by rw [neg_sq, hs], h⟩
  have hns : ¬ V.MM s := by
    intro h
    apply not_mm_one (V := V)
    have := V.v.map_lt_add h (show 0 < V.v (-(s - 1)) by rw [V.v.map_neg]; exact hs1)
    simpa [VF.MM] using this
  have hs0 : s ≠ 0 := by rintro rfl; exact hns (by simp [VF.MM])
  refine ⟨fun c => em c w * s⁻¹, fun c => ?_, fun c => VF.Ge.mul_int (hint c w) (ge_inv hns), fun N => ?_⟩
  · have := hwu c
    field_simp
    linear_combination this + hsu
  · obtain ⟨m, hm⟩ := exists_odd_pow h2 hs1 N
    refine ⟨w * (-(star w * w)) ^ m, fun c => ?_⟩
    have : em c w * s⁻¹ - em c (w * (-(star w * w)) ^ m) = -(em c w * s⁻¹ * (s ^ (2 * m + 1) - 1)) := by
      rw [map_mul, map_pow, map_neg, map_mul, hst, hwu, neg_neg, ← hsu, ← pow_mul]
      field_simp
      ring
    simp only
    rw [this]
    exact (VF.Ge.mul_int (VF.Ge.mul_int (hint c w) (ge_inv hns)) hm).neg

theorem main : ∀ (C : Type) [Field C] [CharZero C] [IsAlgClosed C] (V : VF C), V.l ≠ 2 → (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → ∀ (O : Type) [CommRing O] [StarRing O] (em : ZMod 2 → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → (∃ x, V.v (em 0 x - em 1 x) = 0) → (∀ a x, em a (star x) = em (a + 1) x) → ∃ gm : ZMod 2 → Matrix (Fin 2) (Fin 2) C, (∀ N : ℕ, ∃ M : Matrix (Fin 2) (Fin 2) O, ∀ a r s, V.Ge N (gm a r s - em a (M r s))) ∧ ∀ a (s s' : Fin 2), ∑ r, gm (a + 1) r s * gm a r s' = if s = s' then 0 else 1 := by
  intro C _ _ _ V h2 _ O _ _ em hint hfr hsep hst
  obtain ⟨z, hz, hz0, hzN⟩ := exists_pair h2 O em hint hfr hsep hst
  refine ⟨fun a => !![1, 2⁻¹; z a, -(z a * 2⁻¹)], fun N => ?_, fun a s s' => ?_⟩
  · obtain ⟨y, hy⟩ := hzN N
    obtain ⟨m, hm⟩ := exists_half h2 N
    refine ⟨!![1, m; y, -(y * m)], fun a r s => ?_⟩
    fin_cases r <;> fin_cases s
    · simpa using VF.Ge.zero _
    · simpa using hm
    · simpa using hy a
    · have := ((VF.Ge.mul_int (hz0 a) hm).add (VF.Ge.mul_int (VF.ge_natCast m) (hy a))).neg
      convert this using 1
      simp; ring
  · have := hz a
    fin_cases s <;> fin_cases s' <;> simp [Fin.sum_univ_two]
    · linear_combination this
    · linear_combination (-2⁻¹) * this
    · linear_combination (-2⁻¹) * this
    · linear_combination (4⁻¹) * this

end GlobalTheory.InertHyperbolic
