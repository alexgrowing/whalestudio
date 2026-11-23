import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.TwoRoots

theorem pow_card_pow_natDegree {g : ℕ} [Fact g.Prime] (x : AlgebraicClosure (ZMod g)) :
    x ^ (g ^ (minpoly (ZMod g) x).natDegree) = x := by
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hi
  haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  haveI : Fintype (IntermediateField.adjoin (ZMod g) {x}) := Fintype.ofFinite _
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have h := FiniteField.pow_card y
  rw [Module.card_eq_pow_finrank (K := ZMod g), IntermediateField.adjoin.finrank hi, ZMod.card] at h
  simpa [y] using congrArg Subtype.val h

theorem pow_eq_pow_padicVal {k : Type} [Field k] {n l a : ℕ} (hn : n ≠ 0) (hl : l.Prime) {x y : k}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (h : x ^ (l ^ a) = y ^ (l ^ a)) :
    x ^ (l ^ padicValNat l n) = y ^ (l ^ padicValNat l n) := by
  haveI := Fact.mk hl
  have hy0 : y ≠ 0 := by rintro rfl; simp [hn] at hy
  have h1 : (x / y) ^ n = 1 := by rw [div_pow, hx, hy, div_one]
  have h2 : (x / y) ^ (l ^ a) = 1 := by rw [div_pow, h, div_self (pow_ne_zero _ hy0)]
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hl).1 (orderOf_dvd_of_pow_eq_one h2)
  have h3 : l ^ b ∣ n := hb ▸ orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf (x / y) ∣ l ^ padicValNat l n := by
    rw [hb]; exact pow_dvd_pow _ ((padicValNat_dvd_iff_le hn).1 h3)
  have h5 := orderOf_dvd_iff_pow_eq_one.1 h4
  rwa [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hy0)] at h5

theorem exists_small_degree {g : ℕ} [Fact g.Prime] {x y : AlgebraicClosure (ZMod g)} {L : ℕ}
    (hm : minpoly (ZMod g) x = minpoly (ZMod g) y) (hxy : x ≠ y) (h : x ^ L = y ^ L) :
    ∃ e, 1 ≤ e ∧ e ≤ (minpoly (ZMod g) x).natDegree / 2 ∧ (x ^ L) ^ (g ^ e) = x ^ L := by
  have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hz : IsIntegral (ZMod g) (x ^ L) := Algebra.IsIntegral.isIntegral _
  haveI := IntermediateField.adjoin.finiteDimensional hi
  haveI := IntermediateField.adjoin.finiteDimensional hz
  refine ⟨(minpoly (ZMod g) (x ^ L)).natDegree, minpoly.natDegree_pos hz, ?_, pow_card_pow_natDegree _⟩
  have hle : IntermediateField.adjoin (ZMod g) {x ^ L} ≤ IntermediateField.adjoin (ZMod g) {x} := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
  have hdvd := IntermediateField.finrank_dvd_of_le_right hle
  have hne : Module.finrank (ZMod g) (IntermediateField.adjoin (ZMod g) {x ^ L}) ≠
      Module.finrank (ZMod g) (IntermediateField.adjoin (ZMod g) {x}) := by
    intro he
    have heq := IntermediateField.eq_of_le_of_finrank_eq hle he
    obtain ⟨σ, hσ⟩ := IsConjRoot.exists_algEquiv (show IsConjRoot (ZMod g) y x from hm.symm)
    have hx : x ∈ IntermediateField.adjoin (ZMod g) {x ^ L} := heq ▸ IntermediateField.mem_adjoin_simple_self _ _
    have hfix : IntermediateField.adjoin (ZMod g) {x ^ L} ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, ← IntermediateField.adjoin_simple_le_iff,
        IntermediateField.le_iff_le, Subgroup.zpowers_le, IntermediateField.mem_fixingSubgroup_iff]
      intro t ht
      induction ht using IntermediateField.adjoin_induction with
      | mem t ht => rw [Set.mem_singleton_iff.1 ht, map_pow, hσ, h]
      | algebraMap t => exact σ.commutes t
      | add a b _ _ ha hb => rw [map_add, ha, hb]
      | inv a _ ha => rw [map_inv₀, ha]
      | mul a b _ _ ha hb => rw [map_mul, ha, hb]
    have := (IntermediateField.mem_fixedField_iff _ _).1 (hfix hx) σ (Subgroup.mem_zpowers σ)
    exact hxy (this.symm.trans hσ)
  rw [IntermediateField.adjoin.finrank hi, IntermediateField.adjoin.finrank hz] at hdvd hne
  obtain ⟨c, hc⟩ := hdvd
  have hpos := minpoly.natDegree_pos hi
  rw [Nat.le_div_iff_mul_le two_pos, hc]
  apply Nat.mul_le_mul_left
  rcases c with _ | _ | c
  · omega
  · omega
  · omega

theorem sum_pow_le {g : ℕ} (hg : 2 ≤ g) (m : ℕ) : ∑ e ∈ Finset.Icc 1 m, g ^ e ≤ 2 * g ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), pow_succ]
    nlinarith [Nat.zero_le (g ^ m)]

theorem card_le_nat (g : ℕ) [Fact g.Prime] (d l : ℕ) (hd : 2 ≤ d) (hl : l.Prime) :
    ((sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)),
      ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y).card ≤
      l ^ padicValNat l (g ^ d - 1) * g ^ (d / 2) := by
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  set S := (sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)),
      ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y with hS
  set L := l ^ padicValNat l (g ^ d - 1) with hL
  have hL0 : 0 < L := pow_pos hl.pos _
  let Q : ℕ → (AlgebraicClosure (ZMod g))[X] := fun e => X ^ (L * g ^ e) - X ^ L
  have hQ : ∀ e, 1 ≤ e → (Q e).natDegree = L * g ^ e := by
    intro e he
    have : 1 < g ^ e := Nat.one_lt_pow (by omega) hg
    rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow, natDegree_X_pow]; nlinarith
  let B : Finset (AlgebraicClosure (ZMod g)) := (Finset.Icc 1 (d / 2)).biUnion fun e => (Q e).roots.toFinset
  have hB : B.card ≤ 2 * (L * g ^ (d / 2)) := by
    calc B.card ≤ ∑ e ∈ Finset.Icc 1 (d / 2), (Q e).roots.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ e ∈ Finset.Icc 1 (d / 2), L * g ^ e := by
        refine Finset.sum_le_sum fun e he => ?_
        rw [← hQ e (Finset.mem_Icc.1 he).1]
        exact (Multiset.toFinset_card_le _).trans (card_roots' _)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        have := Nat.mul_le_mul_left L (sum_pow_le hg (d / 2))
        linarith
  have hmemB : ∀ x y : AlgebraicClosure (ZMod g), minpoly (ZMod g) x = minpoly (ZMod g) y →
      (minpoly (ZMod g) x).natDegree = d → x ≠ y → x ^ L = y ^ L → x ∈ B := by
    intro x y h1 h2 h3 h4
    obtain ⟨e, he1, he2, he3⟩ := exists_small_degree h1 h3 h4
    rw [h2] at he2
    refine Finset.mem_biUnion.2 ⟨e, Finset.mem_Icc.2 ⟨he1, he2⟩, ?_⟩
    have hQ0 : Q e ≠ 0 := by
      intro h0
      have := hQ e he1
      rw [h0, natDegree_zero] at this
      have : 0 < L * g ^ e := by positivity
      omega
    rw [Multiset.mem_toFinset, mem_roots hQ0]
    simp [Q, pow_mul, he3]
  have hcount : 2 * S.card ≤ (B.filter fun x => minpoly (ZMod g) x ∈ S).card := by
    refine Finset.mul_card_image_le_card_of_maps_to (f := fun x => minpoly (ZMod g) x)
      (fun a ha => (Finset.mem_filter.1 ha).2) 2 ?_
    intro P hP
    obtain ⟨hP1, hirr, x, hx, y, hy, hxy, hs⟩ := Finset.mem_filter.1 hP
    obtain ⟨hmon, hdeg, -, h0⟩ := mem_sqSet.1 hP1
    have ex := (minpoly.eq_of_irreducible_of_monic hirr (mem_aroots.1 hx).2 hmon).symm
    have ey := (minpoly.eq_of_irreducible_of_monic hirr (mem_aroots.1 hy).2 hmon).symm
    have hx0 := root_ne_zero h0 hx
    have hy0 := root_ne_zero h0 hy
    have hgd : 1 < g ^ d := Nat.one_lt_pow (by omega) hg
    have hroot : ∀ t : AlgebraicClosure (ZMod g), t ≠ 0 → minpoly (ZMod g) t = P → t ^ (g ^ d - 1) = 1 := by
      intro t ht et
      have := pow_card_pow_natDegree t
      rw [et, hdeg] at this
      apply mul_right_cancel₀ ht
      rw [← pow_succ, Nat.sub_add_cancel hgd.le, this, one_mul]
    obtain ⟨a, ha⟩ := (samePart_iff_of_ne_zero hl hx0 hy0).1 hs
    have hLxy : x ^ L = y ^ L := pow_eq_pow_padicVal (by omega) hl (hroot x hx0 ex) (hroot y hy0 ey) ha
    have hxB := hmemB x y (ex.trans ey.symm) (by rw [ex, hdeg]) hxy hLxy
    have hyB := hmemB y x (ey.trans ex.symm) (by rw [ey, hdeg]) hxy.symm hLxy.symm
    rw [← Finset.card_pair hxy]
    apply Finset.card_le_card
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    simp only [Finset.mem_filter]
    rcases ht with rfl | rfl
    · exact ⟨⟨hxB, by rw [ex]; exact hP⟩, ex⟩
    · exact ⟨⟨hyB, by rw [ey]; exact hP⟩, ey⟩
  have := hcount.trans ((Finset.card_filter_le _ _).trans hB)
  omega

theorem card_irreducible_samePart_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N d l : ℕ), 2 ≤ d → d ≤ N → l.Prime → ¬ BB g N l → (((sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)), ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y).card : ℝ) ≤ (g : ℝ) ^ ((3 * d : ℝ) / 4) := by
  intro g _ N d l hd hN hl hb
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have h1 := card_le_nat g d l hd hl
  have h2 : (l ^ padicValNat l (g ^ d - 1)) ^ 4 ≤ g ^ d := by
    by_contra hc
    exact hb (bb_iff.2 (Or.inr ⟨hl, d, by omega, hN, by rw [mul_comm, pow_mul]; omega⟩))
  have h3 : ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ) ≤ (g : ℝ) ^ ((d : ℝ) / 4) := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
    rw [← Real.rpow_natCast ((g : ℝ) ^ ((d : ℝ) / 4)), ← Real.rpow_mul (by positivity)]
    have : (d : ℝ) / 4 * (4 : ℕ) = d := by push_cast; ring
    rw [this, Real.rpow_natCast]
    exact_mod_cast h2
  have h4 : ((g ^ (d / 2) : ℕ) : ℝ) ≤ (g : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hg1 (by exact_mod_cast Nat.cast_div_le (α := ℝ) (m := d) (n := 2))
  calc _ ≤ ((l ^ padicValNat l (g ^ d - 1) * g ^ (d / 2) : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (g : ℝ) ^ ((d : ℝ) / 4) * (g : ℝ) ^ ((d : ℝ) / 2) := by
      rw [Nat.cast_mul]; exact mul_le_mul h3 h4 (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end GlobalTheory.BadShare.TwoRoots
