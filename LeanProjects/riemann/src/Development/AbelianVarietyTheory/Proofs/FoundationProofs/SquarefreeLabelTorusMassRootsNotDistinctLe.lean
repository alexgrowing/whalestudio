import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassSamePartOneFactorLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassTwoFactorsLe

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

open Polynomial Classical in
private theorem pow_card_pow_natDegree_minpoly_sub_one_eq_one {g : ℕ} [Fact g.Prime] (x : AlgebraicClosure (ZMod g)) (hx : x ≠ 0) :
    x ^ (g ^ (minpoly (ZMod g) x).natDegree - 1) = 1 := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  let K := IntermediateField.adjoin (ZMod g) {x}
  have hfin : Module.finrank (ZMod g) K = (minpoly (ZMod g) x).natDegree :=
    IntermediateField.adjoin.finrank hint
  haveI : FiniteDimensional (ZMod g) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = g ^ (minpoly (ZMod g) x).natDegree := by
    rw [← hfin, Module.card_eq_pow_finrank (K := ZMod g), ZMod.card]
  let x' : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ _⟩
  have hx' : x' ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have := FiniteField.pow_card_sub_one_eq_one x' hx'
  rw [hcard] at this
  exact congrArg Subtype.val this

open Polynomial Classical in
private theorem mem_primeFactors_mul_of_same_of_ne {g : ℕ} [Fact g.Prime] (l : ℕ) (hl : l.Prime) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (x y : AlgebraicClosure (ZMod g)) (hx : x ^ n = 1) (hy : y ^ m = 1) (hxy : x ≠ y)
    (hs : _root_.GlobalTheory.BadShare.SamePart l x y) : l ∈ (n * m).primeFactors := by
  have hx0 : x ≠ 0 := by rintro rfl; simp [zero_pow hn.ne'] at hx
  have hy0 : y ≠ 0 := by rintro rfl; simp [zero_pow hm.ne'] at hy
  obtain ⟨a, ha⟩ := (_root_.GlobalTheory.BadShare.samePart_iff_of_ne_zero hl hx0 hy0).1 hs
  rw [Nat.mem_primeFactors]
  refine ⟨hl, ?_, by positivity⟩
  by_contra hdiv
  have hcop : (n * m).Coprime l := (Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hdiv)
  exact hxy (_root_.GlobalTheory.BadShare.eq_of_pow_eq (M := n * m) (l := l) (a := a) hcop
    (by rw [pow_mul, hx, one_pow]) (by rw [mul_comm, pow_mul, hy, one_pow]) (by positivity) ha)

open Polynomial Classical in
private theorem isCoprime_minpoly_of_ne {g : ℕ} [Fact g.Prime] {x y : AlgebraicClosure (ZMod g)}
    (h : minpoly (ZMod g) x ≠ minpoly (ZMod g) y) : IsCoprime (minpoly (ZMod g) x) (minpoly (ZMod g) y) := by
  have hix : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hiy : IsIntegral (ZMod g) y := Algebra.IsIntegral.isIntegral y
  refine (minpoly.irreducible hix).coprime_iff_not_dvd.2 fun hd => h ?_
  exact eq_of_monic_of_associated (minpoly.monic hix) (minpoly.monic hiy)
    ((minpoly.irreducible hix).associated_of_dvd (minpoly.irreducible hiy) hd)

open Polynomial Classical in
private theorem exists_root_pow_eq_pow_padicVal {g : ℕ} [Fact g.Prime] (l : ℕ) (hl : l.Prime) (n : ℕ) (hn : 0 < n)
    (y : AlgebraicClosure (ZMod g)) (hy : y ^ n = 1) :
    ∃ z : AlgebraicClosure (ZMod g), z ^ (n / l ^ padicValNat l n) = 1 ∧
      z ^ l ^ padicValNat l n = y ^ l ^ padicValNat l n := by
  set B := padicValNat l n
  set m := n / l ^ B
  have hnm : n = l ^ B * m := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
  have hm0 : m ≠ 0 := by rintro h; rw [h, mul_zero] at hnm; omega
  have hcop : (l ^ B).Coprime m := by
    have := Nat.coprime_ordCompl hl hn.ne'
    rw [Nat.factorization_def n hl] at this
    exact Nat.Coprime.pow_left _ this
  haveI : NeZero m := ⟨hm0⟩
  obtain ⟨t, ht⟩ : ∃ t, l ^ B * t ≡ 1 [MOD m] := by
    refine ⟨(((l ^ B : ℕ) : ZMod m)⁻¹).val, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ hcop
  refine ⟨y ^ (l ^ B * t), ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← mul_assoc, mul_comm m, ← hnm, pow_mul, hy, one_pow]
  · have hw : (y ^ l ^ B) ^ m = 1 := by rw [← pow_mul, ← hnm, hy]
    have key : ∀ a, (y ^ l ^ B) ^ a = (y ^ l ^ B) ^ (a % m) := fun a => by
      conv_lhs => rw [← Nat.div_add_mod a m, pow_add, pow_mul, hw, one_pow, one_mul]
    rw [← pow_mul, mul_comm, pow_mul, key, ht, ← key, pow_one]

open Polynomial Classical in
private theorem pow_pow_gcd_sub_one_eq_one_of_same_prime_power {g : ℕ} [Fact g.Prime] (l : ℕ) (hl : l.Prime) (d e : ℕ) (he : 0 < g ^ e - 1)
    (x y z : AlgebraicClosure (ZMod g)) (hx : x ^ (g ^ d - 1) = 1)
    (a : ℕ) (ha : x ^ l ^ a = y ^ l ^ a)
    (hz : z ^ ((g ^ e - 1) / l ^ padicValNat l (g ^ e - 1)) = 1)
    (hzy : z ^ l ^ padicValNat l (g ^ e - 1) = y ^ l ^ padicValNat l (g ^ e - 1)) :
    z ^ (g ^ Nat.gcd d e - 1) = 1 := by
  set B := padicValNat l (g ^ e - 1)
  set m := (g ^ e - 1) / l ^ B
  have hnm : g ^ e - 1 = l ^ B * m := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
  have hcop : (l ^ (max a B)).Coprime m := by
    have := Nat.coprime_ordCompl hl he.ne'
    rw [Nat.factorization_def _ hl] at this
    exact Nat.Coprime.pow_left _ this
  have hK : z ^ l ^ max a B = x ^ l ^ max a B := by
    have h1 : z ^ l ^ max a B = y ^ l ^ max a B := by
      rw [← Nat.sub_add_cancel (le_max_right a B), pow_add, mul_comm, pow_mul, pow_mul, hzy]
    have h2 : x ^ l ^ max a B = y ^ l ^ max a B := by
      rw [← Nat.sub_add_cancel (le_max_left a B), pow_add, mul_comm, pow_mul, pow_mul, ha]
    rw [h1, h2]
  have h3 : z ^ (l ^ max a B * (g ^ d - 1)) = 1 := by
    rw [pow_mul, hK, ← pow_mul, mul_comm, pow_mul, hx, one_pow]
  have h4 : z ^ Nat.gcd (l ^ max a B * (g ^ d - 1)) m = 1 := pow_gcd_eq_one.2 ⟨h3, hz⟩
  rw [Nat.Coprime.gcd_mul_left_cancel _ hcop] at h4
  have hzd : z ^ (g ^ d - 1) = 1 := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left (g ^ d - 1) m
    rw [hk, pow_mul, h4, one_pow]
  have hze : z ^ (g ^ e - 1) = 1 := by rw [hnm, mul_comm, pow_mul, hz, one_pow]
  have := pow_gcd_eq_one.2 ⟨hzd, hze⟩
  rwa [Nat.pow_sub_one_gcd_pow_sub_one] at this

open Polynomial Classical in
private theorem card_nthRoots_samePrimePower_le {g : ℕ} [Fact g.Prime] (l n : ℕ) (hl : l.Prime) (hn : 0 < n) (z : AlgebraicClosure (ZMod g)) :
    ((nthRoots n (1 : AlgebraicClosure (ZMod g))).toFinset.filter (fun x => _root_.GlobalTheory.BadShare.SamePart l x z)).card ≤
      l ^ padicValNat l n := by
  obtain ⟨hfin, hle⟩ := (_root_.GlobalTheory.BadShare.samePart_roots_finite_ncard (AlgebraicClosure (ZMod g)) n l hn hl).2 z
  refine le_trans ?_ hle
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ hfin
  intro x hx
  simp only [Finset.coe_filter, Multiset.mem_toFinset, mem_nthRoots hn, Set.mem_setOf_eq] at hx ⊢
  exact hx

open Polynomial Classical in
private theorem card_root_pairs_samePrimePower_le {g : ℕ} [Fact g.Prime] (l : ℕ) (hl : l.Prime) (d e : ℕ)
    (hd : 0 < g ^ d - 1) (he : 0 < g ^ e - 1) :
    (((nthRoots (g ^ d - 1) (1 : AlgebraicClosure (ZMod g))).toFinset ×ˢ
        (nthRoots (g ^ e - 1) (1 : AlgebraicClosure (ZMod g))).toFinset).filter
          (fun p => _root_.GlobalTheory.BadShare.SamePart l p.1 p.2)).card ≤
      (g ^ Nat.gcd d e - 1) * l ^ padicValNat l (g ^ e - 1) * l ^ padicValNat l (g ^ d - 1) := by
  set Xd := (nthRoots (g ^ d - 1) (1 : AlgebraicClosure (ZMod g))).toFinset
  set Ye := (nthRoots (g ^ e - 1) (1 : AlgebraicClosure (ZMod g))).toFinset
  set Rc := (nthRoots (g ^ Nat.gcd d e - 1) (1 : AlgebraicClosure (ZMod g))).toFinset
  set Y' := Rc.biUnion (fun z => Ye.filter (fun y => _root_.GlobalTheory.BadShare.SamePart l y z))
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, pow_zero] at hd; omega
    · exact h
  have hcpos : 0 < g ^ Nat.gcd d e - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.gcd_pos_of_pos_left e hd0).ne' hg1)
  have hsub : (Xd ×ˢ Ye).filter (fun p => _root_.GlobalTheory.BadShare.SamePart l p.1 p.2) ⊆
      Y'.biUnion (fun y => (Xd.filter (fun x => _root_.GlobalTheory.BadShare.SamePart l x y)) ×ˢ {y}) := by
    rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Xd, Ye, Multiset.mem_toFinset, mem_nthRoots hd,
      mem_nthRoots he] at hp
    obtain ⟨⟨hx, hy⟩, hs⟩ := hp
    have hx0 : x ≠ 0 := by rintro rfl; simp [zero_pow hd.ne'] at hx
    have hy0 : y ≠ 0 := by rintro rfl; simp [zero_pow he.ne'] at hy
    obtain ⟨a, ha⟩ := (_root_.GlobalTheory.BadShare.samePart_iff_of_ne_zero hl hx0 hy0).1 hs
    obtain ⟨z, hz, hzy⟩ := exists_root_pow_eq_pow_padicVal l hl _ he y hy
    have hc : z ^ (g ^ Nat.gcd d e - 1) = 1 := pow_pow_gcd_sub_one_eq_one_of_same_prime_power l hl d e he x y z hx a ha hz hzy
    have hz0 : z ≠ 0 := by rintro rfl; simp [zero_pow hcpos.ne'] at hc
    simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_filter, Finset.mem_singleton, Y', Rc, Xd, Ye,
      Multiset.mem_toFinset, mem_nthRoots hd, mem_nthRoots he, mem_nthRoots hcpos]
    exact ⟨y, ⟨z, hc, hy, (_root_.GlobalTheory.BadShare.samePart_iff_of_ne_zero hl hy0 hz0).2 ⟨_, hzy.symm⟩⟩, ⟨hx, hs⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le).trans ?_
  have h1 : ∀ y ∈ Y', ((Xd.filter (fun x => _root_.GlobalTheory.BadShare.SamePart l x y)) ×ˢ {y}).card ≤ l ^ padicValNat l (g ^ d - 1) := by
    intro y _
    rw [Finset.card_product, Finset.card_singleton, mul_one]
    exact card_nthRoots_samePrimePower_le l _ hl hd y
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  refine (Finset.card_biUnion_le).trans ?_
  refine (Finset.sum_le_sum (fun z _ => card_nthRoots_samePrimePower_le l _ hl he z)).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots _ _)

open Polynomial Classical in
private theorem mass_pairFor_le {g : ℕ} [Fact g.Prime] (N l : ℕ) (hl : l.Prime) (d e : ℕ) (hd1 : 1 ≤ d) (he1 : 1 ≤ e) :
    _root_.GlobalTheory.BadShare.mass g N (_root_.GlobalTheory.BadShare.TwoFactors.PairFor d e l) ≤
      (((g ^ Nat.gcd d e - 1) * l ^ padicValNat l (g ^ e - 1) * l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ) /
        (((g ^ d - 1 : ℕ) : ℝ) * ((g ^ e - 1 : ℕ) : ℝ)) := by
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hd : 0 < g ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hg1)
  have he : 0 < g ^ e - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hg1)
  set S := (((nthRoots (g ^ d - 1) (1 : AlgebraicClosure (ZMod g))).toFinset ×ˢ
        (nthRoots (g ^ e - 1) (1 : AlgebraicClosure (ZMod g))).toFinset).filter
          (fun p => _root_.GlobalTheory.BadShare.SamePart l p.1 p.2)).filter (fun p => (minpoly (ZMod g) p.1).natDegree = d ∧
            (minpoly (ZMod g) p.2).natDegree = e ∧ minpoly (ZMod g) p.1 ≠ minpoly (ZMod g) p.2) with hS
  have hU := (_root_.GlobalTheory.BadShare.mass_union_bounds g N).2.2.1 _ S (_root_.GlobalTheory.BadShare.TwoFactors.PairFor d e l)
    (fun p f => minpoly (ZMod g) p.1 * minpoly (ZMod g) p.2 ∣ f) (by
      intro f _ ⟨x, y, hx, hy, hs, hdx, hdy, hne', hPf, hQf⟩
      refine ⟨(x, y), ?_, (isCoprime_minpoly_of_ne hne').mul_dvd hPf hQf⟩
      rw [hS, Finset.mem_filter, Finset.mem_filter, Finset.mem_product, Multiset.mem_toFinset, Multiset.mem_toFinset,
        mem_nthRoots hd, mem_nthRoots he]
      exact ⟨⟨⟨hx, hy⟩, hs⟩, hdx, hdy, hne'⟩)
  refine hU.trans ?_
  have hterm : ∀ p ∈ S, _root_.GlobalTheory.BadShare.mass g N (fun f => minpoly (ZMod g) p.1 * minpoly (ZMod g) p.2 ∣ f) ≤
      1 / (((g ^ d - 1 : ℕ) : ℝ) * ((g ^ e - 1 : ℕ) : ℝ)) := by
    rintro ⟨x, y⟩ hp
    rw [hS, Finset.mem_filter, Finset.mem_filter, Finset.mem_product, Multiset.mem_toFinset, Multiset.mem_toFinset,
        mem_nthRoots hd, mem_nthRoots he] at hp
    obtain ⟨⟨⟨hx, hy⟩, -⟩, hdx, hdy, hne'⟩ := hp
    have hix : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
    have hiy : IsIntegral (ZMod g) y := Algebra.IsIntegral.isIntegral y
    have hx0 : x ≠ 0 := by rintro rfl; simp [zero_pow hd.ne'] at hx
    have hy0 : y ≠ 0 := by rintro rfl; simp [zero_pow he.ne'] at hy
    have hmem : minpoly (ZMod g) x * minpoly (ZMod g) y ∈ _root_.GlobalTheory.BadShare.sqSet g (d + e) := by
      rw [_root_.GlobalTheory.BadShare.mem_sqSet]
      refine ⟨(minpoly.monic hix).mul (minpoly.monic hiy), ?_, ?_, ?_⟩
      · rw [natDegree_mul (minpoly.ne_zero hix) (minpoly.ne_zero hiy), hdx, hdy]
      · exact squarefree_mul_iff.2 ⟨(isCoprime_minpoly_of_ne hne').isRelPrime,
          (minpoly.irreducible hix).squarefree, (minpoly.irreducible hiy).squarefree⟩
      · rw [mul_coeff_zero]
        exact mul_ne_zero (minpoly.coeff_zero_ne_zero hix hx0) (minpoly.coeff_zero_ne_zero hiy hy0)
    refine ((_root_.GlobalTheory.BadShare.divisor_bound g).2 N _ _ hmem).trans (le_of_eq ?_)
    rw [_root_.GlobalTheory.BadShare.torusCard_mul (minpoly.ne_zero hix) (minpoly.ne_zero hiy),
      _root_.GlobalTheory.BadShare.torusCard_irreducible (minpoly.irreducible hix),
      _root_.GlobalTheory.BadShare.torusCard_irreducible (minpoly.irreducible hiy), hdx, hdy, one_div, Nat.cast_mul]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  gcongr
  exact_mod_cast (Finset.card_filter_le _ _).trans (card_root_pairs_samePrimePower_le l hl d e hd he)

open Polynomial Classical in
private theorem pair_ratio_le_of_not_bb {g : ℕ} [Fact g.Prime] (hg : 2 ^ 12 ≤ g) (N l d e : ℕ) (hd1 : 1 ≤ d) (he1 : 1 ≤ e)
    (hdN : d ≤ N) (heN : e ≤ N) (hl : l.Prime) (hexc : ¬ _root_.GlobalTheory.BadShare.BB g N l) :
    (((g ^ Nat.gcd d e - 1) * l ^ padicValNat l (g ^ e - 1) * l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ) /
        (((g ^ d - 1 : ℕ) : ℝ) * ((g ^ e - 1 : ℕ) : ℝ)) ≤
      (4096 / 4095) ^ 2 * (1 / (g : ℝ) ^ ((1 : ℝ) / 4)) ^ (d + e) := by
  rw [_root_.GlobalTheory.BadShare.bb_iff] at hexc
  push_neg at hexc
  obtain ⟨-, hexc⟩ := hexc
  have hPd : (l ^ padicValNat l (g ^ d - 1)) ^ 4 ≤ g ^ d := by
    rw [← pow_mul, mul_comm]
    exact hexc hl d hd1 hdN
  have hPe : (l ^ padicValNat l (g ^ e - 1)) ^ 4 ≤ g ^ e := by
    rw [← pow_mul, mul_comm]
    exact hexc hl e he1 heN
  set c := Nat.gcd d e
  have hcd : c ≤ d := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left d e)
  have hce : c ≤ e := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right d e)
  have hnat : ((g ^ c - 1) * l ^ padicValNat l (g ^ e - 1) * l ^ padicValNat l (g ^ d - 1)) ^ 4 ≤
      g ^ (3 * (d + e)) := by
    have h1 : (g ^ c - 1) ^ 4 ≤ g ^ (2 * (d + e)) :=
      (Nat.pow_le_pow_left (Nat.sub_le _ _) 4).trans (by rw [← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by omega))
    calc _ = (g ^ c - 1) ^ 4 * (l ^ padicValNat l (g ^ e - 1)) ^ 4 * (l ^ padicValNat l (g ^ d - 1)) ^ 4 := by
          rw [mul_pow, mul_pow]
      _ ≤ g ^ (2 * (d + e)) * g ^ e * g ^ d := by gcongr
      _ = g ^ (3 * (d + e)) := by rw [← pow_add, ← pow_add]; ring_nf
  set q : ℝ := (g : ℝ) ^ ((1 : ℝ) / 4) with hq
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hq0 : 0 < q := Real.rpow_pos_of_pos hg0 _
  have hq4 : q ^ 4 = g := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hg0.le]; norm_num
  have hX : (((g ^ c - 1) * l ^ padicValNat l (g ^ e - 1) * l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ) ≤
      q ^ (3 * (d + e)) := by
    have h4 : (q ^ (3 * (d + e))) ^ 4 = (g : ℝ) ^ (3 * (d + e)) := by rw [← pow_mul, mul_comm, pow_mul, hq4]
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (4 : ℕ) ≠ 0), h4]
    exact_mod_cast hnat
  have hden : ∀ k, 1 ≤ k → (4095 / 4096 : ℝ) * q ^ (4 * k) ≤ ((g ^ k - 1 : ℕ) : ℝ) := by
    intro k hk
    have hgk : g ≤ g ^ k := Nat.le_self_pow (by omega) g
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one, pow_mul, hq4]
    have : (4096 : ℝ) ≤ (g : ℝ) ^ k := by exact_mod_cast (by omega : 4096 ≤ g ^ k)
    linarith
  have hDd := hden d hd1
  have hDe := hden e he1
  calc _ ≤ q ^ (3 * (d + e)) / ((4095 / 4096 : ℝ) * q ^ (4 * d) * ((4095 / 4096 : ℝ) * q ^ (4 * e))) := by
        gcongr
    _ = (4096 / 4095) ^ 2 * (1 / q) ^ (d + e) := by
        rw [one_div, inv_pow]
        field_simp
        ring

open Polynomial Classical in
private theorem card_primeFactors_le_logb_two (n : ℕ) (hn : n ≠ 0) : (n.primeFactors.card : ℝ) ≤ Real.logb 2 n := by
  have h : 2 ^ n.primeFactors.card ≤ n := by
    refine (Finset.pow_card_le_prod _ _ 2 fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le).trans ?_
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero hn), Real.rpow_natCast]
  exact_mod_cast h

open Polynomial Classical in
private theorem sum_icc_prod_add_mul_pow_le (N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ de ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, ((de.1 + de.2 : ℕ) : ℝ) * r ^ (de.1 + de.2) ≤
      2 * r ^ 2 / (1 - r) ^ 3 := by
  have hA : ∑ d ∈ Finset.Icc 1 N, (d : ℝ) * r ^ d ≤ r / (1 - r) ^ 2 := by
    have hs : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
    rw [← tsum_coe_mul_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])]
    exact hs.sum_le_tsum _ (fun i _ => by positivity)
  have hB : ∑ e ∈ Finset.Icc 1 N, r ^ e ≤ r / (1 - r) := by
    have hs : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
    calc ∑ e ∈ Finset.Icc 1 N, r ^ e = r * ∑ e ∈ Finset.Icc 1 N, r ^ (e - 1) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun e he => ?_
          rw [← pow_succ']; congr 1; have := (Finset.mem_Icc.1 he).1; omega
      _ ≤ r * ∑' n : ℕ, r ^ n := by
          gcongr
          calc ∑ e ∈ Finset.Icc 1 N, r ^ (e - 1) = ∑ n ∈ Finset.range N, r ^ n := by
                rw [Finset.range_eq_Ico]
                exact Finset.sum_nbij' (fun e => e - 1) (fun n => n + 1) (by intro a ha; simp at ha ⊢; omega)
                  (by intro a ha; simp at ha ⊢; omega) (by intro a ha; simp at ha; omega) (by intro a ha; simp)
                  (by intro a ha; rfl)
            _ ≤ ∑' n : ℕ, r ^ n := hs.sum_le_tsum _ (fun i _ => by positivity)
      _ = r / (1 - r) := by rw [tsum_geometric_of_lt_one hr0 hr1]; ring
  have hsplit : ∑ de ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, ((de.1 + de.2 : ℕ) : ℝ) * r ^ (de.1 + de.2) =
      2 * ((∑ d ∈ Finset.Icc 1 N, (d : ℝ) * r ^ d) * ∑ e ∈ Finset.Icc 1 N, r ^ e) := by
    rw [Finset.sum_product, Finset.sum_mul_sum]
    have : ∀ d e : ℕ, ((d + e : ℕ) : ℝ) * r ^ (d + e) = (d : ℝ) * r ^ d * r ^ e + (e : ℝ) * r ^ e * r ^ d := by
      intro d e; push_cast; rw [pow_add]; ring
    simp only [this, Finset.sum_add_distrib]
    nth_rewrite 2 [Finset.sum_comm]
    ring
  rw [hsplit]
  have h1r : 0 < 1 - r := by linarith
  calc 2 * ((∑ d ∈ Finset.Icc 1 N, (d : ℝ) * r ^ d) * ∑ e ∈ Finset.Icc 1 N, r ^ e)
      ≤ 2 * (r / (1 - r) ^ 2 * (r / (1 - r))) := by
        gcongr
    _ = 2 * r ^ 2 / (1 - r) ^ 3 := by field_simp <;> ring

open Polynomial Classical in

theorem _root_.GlobalTheory.BadShare.mass_not_rootsApart_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 2 ^ 12 ≤ g →
    (_root_.GlobalTheory.BadShare.mass g N fun f => ¬ _root_.GlobalTheory.BadShare.RootsApart g N f) ≤ 23 * Real.log g / Real.sqrt g := by
  intro g _ N hg
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  set L : ℕ × ℕ → Finset ℕ := fun de =>
    ((g ^ de.1 - 1) * (g ^ de.2 - 1)).primeFactors.filter (fun l => ¬ _root_.GlobalTheory.BadShare.BB g N l) with hL
  set s := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).sigma L with hs
  set One : (ZMod g)[X] → Prop := fun f => ∃ l, Nat.Prime l ∧ ¬_root_.GlobalTheory.BadShare.BB g N l ∧
      ∃ P : (ZMod g)[X], P.Monic ∧ Irreducible P ∧ P ∣ f ∧
      ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)), ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)),
        x ≠ y ∧ _root_.GlobalTheory.BadShare.SamePart l x y with hOne
  set B : Option ((_ : ℕ × ℕ) × ℕ) → (ZMod g)[X] → Prop := fun i => match i with
    | none => One
    | some t => _root_.GlobalTheory.BadShare.TwoFactors.PairFor t.1.1 t.1.2 t.2 with hB
  have hU := (_root_.GlobalTheory.BadShare.mass_union_bounds g N).2.2.1 _ (Finset.insertNone s)
    (fun f => ¬ _root_.GlobalTheory.BadShare.RootsApart g N f) B (by
      intro f hf hnot
      rw [_root_.GlobalTheory.BadShare.mem_sqSet] at hf
      obtain ⟨hmon, hdeg, -, hc⟩ := hf
      have hf0 : f ≠ 0 := hmon.ne_zero
      unfold _root_.GlobalTheory.BadShare.RootsApart at hnot
      push_neg at hnot
      obtain ⟨l, hl, hexc, x, hx, y, hy, hsame, hxy⟩ := hnot
      have hix : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
      have hiy : IsIntegral (ZMod g) y := Algebra.IsIntegral.isIntegral y
      have hPf : minpoly (ZMod g) x ∣ f := minpoly.dvd _ _ (mem_aroots.mp hx).2
      have hQf : minpoly (ZMod g) y ∣ f := minpoly.dvd _ _ (mem_aroots.mp hy).2
      by_cases hPQ : minpoly (ZMod g) x = minpoly (ZMod g) y
      · refine ⟨none, Finset.none_mem_insertNone, ?_⟩
        refine ⟨l, hl, hexc, minpoly (ZMod g) x, minpoly.monic hix, minpoly.irreducible hix, hPf, x, ?_, y, ?_,
          hxy, hsame⟩
        · exact mem_aroots.mpr ⟨minpoly.ne_zero hix, minpoly.aeval _ _⟩
        · rw [hPQ]; exact mem_aroots.mpr ⟨minpoly.ne_zero hiy, minpoly.aeval _ _⟩
      · have hdx : 1 ≤ (minpoly (ZMod g) x).natDegree := minpoly.natDegree_pos hix
        have hdy : 1 ≤ (minpoly (ZMod g) y).natDegree := minpoly.natDegree_pos hiy
        have hlx : (minpoly (ZMod g) x).natDegree ≤ N := hdeg ▸ natDegree_le_of_dvd hPf hf0
        have hly : (minpoly (ZMod g) y).natDegree ≤ N := hdeg ▸ natDegree_le_of_dvd hQf hf0
        have hpx := pow_card_pow_natDegree_minpoly_sub_one_eq_one x (_root_.GlobalTheory.BadShare.root_ne_zero hc hx)
        have hpy := pow_card_pow_natDegree_minpoly_sub_one_eq_one y (_root_.GlobalTheory.BadShare.root_ne_zero hc hy)
        have hdpos : 0 < g ^ (minpoly (ZMod g) x).natDegree - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hg1)
        have hepos : 0 < g ^ (minpoly (ZMod g) y).natDegree - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hg1)
        refine ⟨some ⟨((minpoly (ZMod g) x).natDegree, (minpoly (ZMod g) y).natDegree), l⟩, ?_, ?_⟩
        · rw [Finset.some_mem_insertNone, hs, Finset.mem_sigma, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc, hL,
            Finset.mem_filter]
          exact ⟨⟨⟨hdx, hlx⟩, hdy, hly⟩, mem_primeFactors_mul_of_same_of_ne l hl _ _ hdpos hepos x y hpx hpy hxy hsame,
            hexc⟩
        · exact ⟨x, y, hpx, hpy, hsame, rfl, rfl, hPQ, hPf, hQf⟩)
  refine hU.trans ?_
  rw [Finset.sum_insertNone]
  have hOne' : _root_.GlobalTheory.BadShare.mass g N (B none) ≤ 12 * Real.logb 2 g / Real.sqrt g :=
    _root_.GlobalTheory.BadShare.mass_samePart_one_factor g N hg
  have hTwo : ∑ t ∈ s, _root_.GlobalTheory.BadShare.mass g N (B (some t)) ≤ 7 / 2 * Real.logb 2 g / Real.sqrt g := by
    set q : ℝ := (g : ℝ) ^ ((1 : ℝ) / 4) with hq
    have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    have hq0 : 0 < q := Real.rpow_pos_of_pos hg0 _
    have hq4 : q ^ 4 = g := by rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hg0.le]; norm_num
    have hq2 : q ^ 2 = Real.sqrt g := by
      rw [Real.sqrt_eq_rpow, hq, ← Real.rpow_natCast, ← Real.rpow_mul hg0.le]; norm_num
    have hq8 : 8 ≤ q := by
      rw [← pow_le_pow_iff_left₀ (by norm_num) hq0.le (by norm_num : (4 : ℕ) ≠ 0), hq4]
      have : (4096 : ℝ) ≤ g := by exact_mod_cast hg
      linarith
    set r : ℝ := 1 / q with hr
    have hr0 : 0 ≤ r := by positivity
    have hr8 : r ≤ 1 / 8 := by rw [hr]; exact one_div_le_one_div_of_le (by norm_num) hq8
    have hr2 : r ^ 2 = 1 / Real.sqrt g := by rw [hr, div_pow, one_pow, hq2]
    have hlb : 0 ≤ Real.logb 2 g := Real.logb_nonneg (by norm_num) (by exact_mod_cast hg1.le)
    rw [hs, Finset.sum_sigma]
    calc _ ≤ ∑ de ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, ∑ l ∈ L de, (4096 / 4095 : ℝ) ^ 2 * r ^ (de.1 + de.2) := by
          refine Finset.sum_le_sum fun de hde => Finset.sum_le_sum fun l hl => ?_
          rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hde
          rw [hL, Finset.mem_filter] at hl
          have hlp : l.Prime := Nat.prime_of_mem_primeFactors hl.1
          exact (mass_pairFor_le N l hlp de.1 de.2 hde.1.1 hde.2.1).trans
            (pair_ratio_le_of_not_bb hg N l de.1 de.2 hde.1.1 hde.2.1 hde.1.2 hde.2.2 hlp hl.2)
      _ ≤ ∑ de ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, (Real.logb 2 g * (4096 / 4095 : ℝ) ^ 2) *
            (((de.1 + de.2 : ℕ) : ℝ) * r ^ (de.1 + de.2)) := by
          refine Finset.sum_le_sum fun de hde => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hde
          have h1 := Nat.one_lt_pow (n := de.1) (by omega) hg1
          have h2 := Nat.one_lt_pow (n := de.2) (by omega) hg1
          have hne : (g ^ de.1 - 1) * (g ^ de.2 - 1) ≠ 0 := mul_ne_zero (by omega) (by omega)
          have hle : (g ^ de.1 - 1) * (g ^ de.2 - 1) ≤ g ^ (de.1 + de.2) := by
            rw [pow_add]; exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
          have hcard : ((L de).card : ℝ) ≤ ((de.1 + de.2 : ℕ) : ℝ) * Real.logb 2 g := by
            refine (Nat.cast_le.2 (Finset.card_filter_le _ _)).trans ((card_primeFactors_le_logb_two _ hne).trans ?_)
            calc Real.logb 2 (((g ^ de.1 - 1) * (g ^ de.2 - 1) : ℕ) : ℝ) ≤ Real.logb 2 ((g : ℝ) ^ (de.1 + de.2)) :=
                  Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero hne)
                    (by exact_mod_cast hle)
              _ = ((de.1 + de.2 : ℕ) : ℝ) * Real.logb 2 g := by rw [Real.logb_pow]
          calc ((L de).card : ℝ) * ((4096 / 4095 : ℝ) ^ 2 * r ^ (de.1 + de.2))
              ≤ (((de.1 + de.2 : ℕ) : ℝ) * Real.logb 2 g) * ((4096 / 4095 : ℝ) ^ 2 * r ^ (de.1 + de.2)) :=
                mul_le_mul_of_nonneg_right hcard (by positivity)
            _ = _ := by ring
      _ = (Real.logb 2 g * (4096 / 4095 : ℝ) ^ 2) * ∑ de ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
            (((de.1 + de.2 : ℕ) : ℝ) * r ^ (de.1 + de.2)) := by rw [Finset.mul_sum]
      _ ≤ (Real.logb 2 g * (4096 / 4095 : ℝ) ^ 2) * (2 * r ^ 2 / (7 / 8) ^ 3) := by
          gcongr
          refine (sum_icc_prod_add_mul_pow_le N hr0 (by linarith)).trans ?_
          gcongr
          linarith
      _ = ((4096 / 4095 : ℝ) ^ 2 * 1024 / 343) * (Real.logb 2 g * r ^ 2) := by ring
      _ ≤ 7 / 2 * (Real.logb 2 g * r ^ 2) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 7 / 2 * Real.logb 2 g / Real.sqrt g := by rw [hr2]; ring
  have hlog : Real.logb 2 g = Real.log g / Real.log 2 := rfl
  have hl2 := Real.log_two_gt_d9
  have hlg : 0 ≤ Real.log g := Real.log_nonneg (by exact_mod_cast hg1.le)
  have hsq : 0 < Real.sqrt g := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < g))
  calc _ ≤ 12 * Real.logb 2 g / Real.sqrt g + 7 / 2 * Real.logb 2 g / Real.sqrt g := add_le_add hOne' hTwo
    _ = 31 / 2 / Real.log 2 * Real.log g / Real.sqrt g := by rw [hlog]; ring
    _ ≤ 23 * Real.log g / Real.sqrt g := by
      gcongr
      rw [div_le_iff₀ (by linarith)]
      linarith

end GlobalTheory.BadShare
