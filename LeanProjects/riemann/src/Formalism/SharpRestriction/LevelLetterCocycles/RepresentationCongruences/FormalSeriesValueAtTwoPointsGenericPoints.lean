import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DvdCoeffsOfMemSpanDistinguished
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

namespace ContPA

theorem mem_of_mem_span_pair {R : Type*} [CommRing R] {a b z : R} {J : Ideal R}
    (hz : z ∈ Ideal.span {a, b}) (ha : a ∈ J) (hb : b ∈ J) : z ∈ J := by
  exact (Ideal.span_le.mpr (by simp [Set.insert_subset_iff, ha, hb])) hz

theorem mem_pair_left_of_dvd {R : Type*} [CommRing R] {a b z : R} (h : a ∣ z) :
    z ∈ Ideal.span {a, b} := by
  obtain ⟨c, rfl⟩ := h
  exact Ideal.mul_mem_right c _ (Ideal.subset_span (Set.mem_insert a {b}))

private lemma mem_of_dvd_lemma {R : Type*} [CommRing R] {I : Ideal R} {a b : R} (h : a ∣ b)
    (ha : a ∈ I) : b ∈ I := by
  obtain ⟨c, rfl⟩ := h
  exact I.mul_mem_right c ha

theorem pow_mem_span_of_sub {R : Type*} [CommRing R] {x x' t : R}
    (h : x - x' ∈ Ideal.span {t}) (n a : ℕ) :
    x ^ n ∈ Ideal.span {t ^ (n + 1 - a), x' ^ a} := by
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h
  have hx : x = x' + s * t := by rw [hs]; ring
  rw [hx, add_pow]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hmn : m < n + 1 := Finset.mem_range.mp hm
  by_cases ham : a ≤ m
  · apply mem_of_dvd_lemma (a := x' ^ a)
    · have h1 : x' ^ a ∣ x' ^ m := pow_dvd_pow x' ham
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h1 _) _
    · exact Ideal.subset_span (by simp)
  · apply mem_of_dvd_lemma (a := t ^ (n + 1 - a))
    · have h1 : t ^ (n + 1 - a) ∣ t ^ (n - m) := pow_dvd_pow t (by omega)
      have h2 : t ^ (n - m) ∣ (s * t) ^ (n - m) := by rw [mul_pow]; exact dvd_mul_left _ _
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (h1.trans h2) _) _
    · exact Ideal.subset_span (by simp)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

private lemma isUnit_natCast_sp_complex_sections {l m : ℕ} (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hc : Nat.Coprime l m) : IsUnit (m : O) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  by_contra hm
  have hm' : (m : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hm)
  have hne : (1 : O) ∉ IsLocalRing.maximalIdeal O :=
    (Ideal.ne_top_iff_one _).mp (inferInstance : (IsLocalRing.maximalIdeal O).IsMaximal).ne_top
  apply hne
  have h1 : (a : O) * (l : O) + (b : O) * (m : O) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → O) hab
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hm')

theorem natCast_unit_mul {l : ℕ} [hp : Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    {n : ℕ} (hn : n ≠ 0) : ∃ v : Oˣ, (n : O) = v * (l : O) ^ padicValNat l n := by
  obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := l) (n := n)
  have hnd : ¬ l ∣ m := by
    rintro ⟨c, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := l) hn
    exact ⟨c, by rw [pow_succ, mul_assoc]; exact hm⟩
  have hu := isUnit_natCast_sp_complex_sections hl ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd)
  refine ⟨hu.unit, ?_⟩
  have hc : (n : O) = (l : O) ^ padicValNat l n * (m : O) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → O) hm
  rw [hc, IsUnit.unit_spec, mul_comm]

theorem natCast_ne_zero' {l : ℕ} [Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hl0 : (l : O) ≠ 0) {n : ℕ} (hn : n ≠ 0) : (n : O) ≠ 0 := by
  obtain ⟨v, hv⟩ := natCast_unit_mul hl hn
  rw [hv]
  exact mul_ne_zero v.ne_zero (pow_ne_zero _ hl0)

theorem addVal_l {l : ℕ} (hl0 : (l : O) ≠ 0) :
    IsDiscreteValuationRing.addVal O (l : O) = ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℕ∞) := by
  exact (ENat.coe_toNat ((IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hl0)).symm

theorem addVal_natCast {l : ℕ} [Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hl0 : (l : O) ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    IsDiscreteValuationRing.addVal O (n : O) =
      (((IsDiscreteValuationRing.addVal O (l : O)).toNat * padicValNat l n : ℕ) : ℕ∞) := by
  obtain ⟨v, hv⟩ := natCast_unit_mul hl hn
  rw [hv, AddValuation.map_mul, AddValuation.map_pow, IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, IsDiscreteValuationRing.addVal O (l : O) = k := ⟨_, addVal_l hl0⟩
  rw [hk, ENat.toNat_coe, nsmul_eq_mul]
  push_cast
  ring

theorem l_unit_mul {ϖ : O} (hϖ : Irreducible ϖ) {l : ℕ} (hl0 : (l : O) ≠ 0) :
    ∃ v : Oˣ, (l : O) = v * ϖ ^ (IsDiscreteValuationRing.addVal O (l : O)).toNat := by
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  refine ⟨v, ?_⟩
  rw [IsDiscreteValuationRing.addVal_def _ v hϖ n hv, ENat.toNat_coe]
  exact hv

theorem C_l_pow_dvd {ϖ : O} (hϖ : Irreducible ϖ) {l : ℕ} (hl0 : (l : O) ≠ 0) {n k : ℕ}
    (hk : k ≤ (IsDiscreteValuationRing.addVal O (l : O)).toNat * n) :
    (C ϖ : O⟦X⟧) ^ k ∣ (C (l : O) : O⟦X⟧) ^ n := by
  obtain ⟨v, hv⟩ := l_unit_mul hϖ hl0
  have h : ϖ ^ k ∣ (l : O) ^ n := by
    rw [hv, mul_pow, ← pow_mul]
    exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hk) _
  have h2 := map_dvd (C : O →+* O⟦X⟧) h
  rw [map_pow, map_pow] at h2
  exact h2

private lemma order_unit_mul_X_pow_lemma_3 {K : Type*} [Field K] {w : K⟦X⟧} (hw : IsUnit w) (n : ℕ) :
    (w * X ^ n).order = (n : ℕ∞) := by
  have hw0 : w.order = 0 := by
    obtain ⟨u, rfl⟩ := hw
    have h := congrArg PowerSeries.order u.mul_inv
    rw [PowerSeries.order_mul, PowerSeries.order_one] at h
    have h2 : PowerSeries.order (u : K⟦X⟧) ≤ 0 := by
      rw [← h]; exact le_self_add
    exact le_antisymm h2 (by simp)
  rw [PowerSeries.order_mul, hw0, PowerSeries.order_X_pow, zero_add]

theorem dist_of_map_eq {f : O⟦X⟧} {w : (IsLocalRing.ResidueField O)⟦X⟧} (hw : IsUnit w) (n : ℕ)
    (h : f.map (IsLocalRing.residue O) = w * X ^ n) : IsDist f ∧ wdeg f = n := by
  have hord : (f.map (IsLocalRing.residue O)).order = n := by
    rw [h]; exact order_unit_mul_X_pow_lemma_3 hw n
  refine ⟨?_, ?_⟩
  · unfold IsDist
    intro h0
    rw [h0, PowerSeries.order_zero] at hord
    exact ENat.top_ne_coe n hord
  · unfold wdeg
    rw [hord]
    rfl

theorem dist_X_pow (n : ℕ) : IsDist ((X : O⟦X⟧) ^ n) ∧ wdeg ((X : O⟦X⟧) ^ n) = n := dist_of_map_eq isUnit_one n (by simp)

section P1
variable {l : ℕ} [hlp : Fact l.Prime] {p1 e u : O⟦X⟧}

theorem residue_map_p1_eq (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hp : p1 = C (l : O) * e + u * X ^ l) :
    p1.map (IsLocalRing.residue O) = u.map (IsLocalRing.residue O) * X ^ l := by
  have h0 : IsLocalRing.residue O (l : O) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hl
  have h0' : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]; exact h0
  have h0'' : ((l : ℕ) : (IsLocalRing.ResidueField O)⟦X⟧) = 0 := by
    rw [← map_natCast (C : IsLocalRing.ResidueField O →+* (IsLocalRing.ResidueField O)⟦X⟧) l, h0', map_zero]
  rw [hp]
  simp [h0, h0', h0'']

theorem isDist_p1_pow_wdeg (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hu : IsUnit u)
    (hp : p1 = C (l : O) * e + u * X ^ l) (y : ℕ) :
    IsDist (p1 ^ y) ∧ wdeg (p1 ^ y) = l * y := dist_of_map_eq ((hu.map (PowerSeries.map (IsLocalRing.residue O))).pow y) (l * y)
    (by rw [map_pow, residue_map_p1_eq hl hp, mul_pow, ← pow_mul])

theorem isDist_p1_wdeg (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hu : IsUnit u)
    (hp : p1 = C (l : O) * e + u * X ^ l) : IsDist p1 ∧ wdeg p1 = l := by
  exact dist_of_map_eq (hu.map (PowerSeries.map (IsLocalRing.residue O))) l (residue_map_p1_eq hl hp)

theorem X_pow_expand (hu : IsUnit u) (hp : p1 = C (l : O) * e + u * X ^ l) (a : ℕ) :
    (X : O⟦X⟧) ^ (l * a) = ∑ i ∈ Finset.range (a + 1),
      ((↑(hu.unit⁻¹) : O⟦X⟧) ^ a * (-e) ^ (a - i)) * C ((a.choose i : O) * (l : O) ^ (a - i)) * p1 ^ i := by
  have hinv : (↑(hu.unit⁻¹) : O⟦X⟧) * u = 1 := hu.unit.inv_mul
  have hX : (X : O⟦X⟧) ^ l = ↑(hu.unit⁻¹) * (p1 + -(C (l : O) * e)) := by
    rw [hp]
    linear_combination (-(X ^ l : O⟦X⟧)) * hinv
  rw [pow_mul, hX, mul_pow, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_natCast]
  ring

theorem p1_pow_eq_sum_choose_mul_X_pow_l_pow (hp : p1 = C (l : O) * e + u * X ^ l) (y : ℕ) :
    p1 ^ y = ∑ i ∈ Finset.range (y + 1),
      (u ^ i * e ^ (y - i)) * C ((y.choose i : O) * (l : O) ^ (y - i)) * ((X : O⟦X⟧) ^ l) ^ i := by
  rw [hp, add_comm (C (l : O) * e), add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_natCast]
  ring

theorem addVal_coef (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) {a i : ℕ} (hi : i ≤ a) :
    IsDiscreteValuationRing.addVal O ((a.choose i : O) * (l : O) ^ (a - i)) =
      (((IsDiscreteValuationRing.addVal O (l : O)).toNat * (a - i + padicValNat l (a.choose i)) : ℕ) : ℕ∞) := by
  have hc : a.choose i ≠ 0 := (Nat.choose_pos hi).ne'
  rw [AddValuation.map_mul, addVal_natCast hl hl0 hc, AddValuation.map_pow]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, IsDiscreteValuationRing.addVal O (l : O) = k := ⟨_, addVal_l hl0⟩
  rw [hk, ENat.toNat_coe, nsmul_eq_mul]
  push_cast
  ring

theorem coef_ne_zero (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) {a i : ℕ} (hi : i ≤ a) :
    (a.choose i : O) * (l : O) ^ (a - i) ≠ 0 := mul_ne_zero (natCast_ne_zero' hl hl0 (Nat.choose_pos hi).ne') (pow_ne_zero _ hl0)

variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

theorem content_p1_pow_X_pow_eq_iInf (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) (he : IsUnit e)
    (hu : IsUnit u) (hp : p1 = C (l : O) * e + u * X ^ l) (a y : ℕ) (hy : 1 ≤ y) :
    cont ϖ (p1 ^ y) ((X : O⟦X⟧) ^ (l * a)) =
      ⨅ i ∈ Finset.range (min a (y - 1) + 1),
        (((IsDiscreteValuationRing.addVal O (l : O)).toNat * (a - i + padicValNat l (a.choose i)) : ℕ) : ℕ∞) := by
  obtain ⟨hX, hD⟩ := isDist_p1_wdeg hl hu hp
  have hD' : 1 ≤ wdeg p1 := by rw [hD]; exact hlp.out.one_lt.le
  have key := Mprime_cont hϖ hX hD' (Finset.range (a + 1))
    (fun i => (↑(hu.unit⁻¹) : O⟦X⟧) ^ a * (-e) ^ (a - i))
    (fun i _ => ((hu.unit⁻¹).isUnit.pow _).mul (he.neg.pow _))
    (fun i => (a.choose i : O) * (l : O) ^ (a - i))
    (fun i hi => coef_ne_zero hl hl0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) y
  rw [X_pow_expand hu hp a, key]
  have hset : (Finset.range (a + 1)).filter (· < y) = Finset.range (min a (y - 1) + 1) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hset]
  refine iInf_congr (fun i => iInf_congr (fun hi => ?_))
  have hi' : i ≤ a := by simp only [Finset.mem_range] at hi; omega
  exact addVal_coef hl hl0 hi'

theorem formalSeriesValueAtTwoPoints_genericPoints (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) (he : IsUnit e)
    (hu : IsUnit u) (hp : p1 = C (l : O) * e + u * X ^ l) (y be : ℕ) (hbe : 1 ≤ be) :
    cont ϖ ((X : O⟦X⟧) ^ (l * be)) (p1 ^ y) =
      ⨅ i ∈ Finset.range (min y (be - 1) + 1),
        (((IsDiscreteValuationRing.addVal O (l : O)).toNat * (y - i + padicValNat l (y.choose i)) : ℕ) : ℕ∞) := by
  obtain ⟨hX, hD⟩ := dist_X_pow (O := O) l
  have hD' : 1 ≤ wdeg ((X : O⟦X⟧) ^ l) := by rw [hD]; exact hlp.out.one_lt.le
  have key := Mprime_cont hϖ hX hD' (Finset.range (y + 1))
    (fun i => u ^ i * e ^ (y - i))
    (fun i _ => (hu.pow _).mul (he.pow _))
    (fun i => (y.choose i : O) * (l : O) ^ (y - i))
    (fun i hi => coef_ne_zero hl hl0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) be
  rw [pow_mul, p1_pow_eq_sum_choose_mul_X_pow_l_pow hp y, key]
  have hset : (Finset.range (y + 1)).filter (· < be) = Finset.range (min y (be - 1) + 1) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hset]
  refine iInf_congr (fun i => iInf_congr (fun hi => ?_))
  have hi' : i ≤ y := by simp only [Finset.mem_range] at hi; omega
  exact addVal_coef hl hl0 hi'

theorem content_p1_pow_X_pow_eq_zero (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hu : IsUnit u)
    (hp : p1 = C (l : O) * e + u * X ^ l) (y b : ℕ) (hlt : b < l * y) :
    cont ϖ (p1 ^ y) ((X : O⟦X⟧) ^ b) = 0 := by
  refine le_antisymm ?_ (by simp)
  unfold cont
  refine iSup₂_le fun k hk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · exfalso
    obtain ⟨a', c', hac⟩ := Ideal.mem_span_pair.mp hk
    have hϖ0 : IsLocalRing.residue O ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).mpr
      ((IsLocalRing.mem_maximalIdeal ϖ).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
    have hm := congrArg (PowerSeries.map (IsLocalRing.residue O)) hac
    simp only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero,
      zero_pow hk0.ne', mul_zero, zero_add, residue_map_p1_eq hl hp] at hm
    have e1 : (PowerSeries.map (IsLocalRing.residue O) u * X ^ l) ^ y =
        PowerSeries.map (IsLocalRing.residue O) u ^ y * X ^ (l * y) := by ring
    rw [e1] at hm
    have ho := congrArg PowerSeries.order hm
    rw [PowerSeries.order_mul, order_unit_mul_X_pow_lemma_3 ((hu.map _).pow y), PowerSeries.order_X_pow] at ho
    have h2 : ((l * y : ℕ) : ℕ∞) ≤ PowerSeries.order (PowerSeries.map (IsLocalRing.residue O) c') + ((l * y : ℕ) : ℕ∞) :=
      le_add_self
    rw [ho] at h2
    have h3 : l * y ≤ b := by exact_mod_cast h2
    omega

theorem content_X_pow_p1_pow_eq_zero (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hu : IsUnit u)
    (hp : p1 = C (l : O) * e + u * X ^ l) (B y : ℕ) (hlt : l * y < B) :
    cont ϖ ((X : O⟦X⟧) ^ B) (p1 ^ y) = 0 := by
  refine le_antisymm ?_ (by simp)
  unfold cont
  refine iSup₂_le fun k hk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · exfalso
    obtain ⟨a', c', hac⟩ := Ideal.mem_span_pair.mp hk
    have hϖ0 : IsLocalRing.residue O ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).mpr
      ((IsLocalRing.mem_maximalIdeal ϖ).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
    have hm := congrArg (PowerSeries.map (IsLocalRing.residue O)) hac
    simp only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero,
      zero_pow hk0.ne', mul_zero, zero_add, residue_map_p1_eq hl hp] at hm
    have e1 : (PowerSeries.map (IsLocalRing.residue O) u * X ^ l) ^ y =
        PowerSeries.map (IsLocalRing.residue O) u ^ y * X ^ (l * y) := by ring
    rw [e1] at hm
    have ho := congrArg PowerSeries.order hm
    rw [PowerSeries.order_mul, order_unit_mul_X_pow_lemma_3 ((hu.map _).pow y), PowerSeries.order_X_pow] at ho
    have h2 : (B : ℕ∞) ≤ PowerSeries.order (PowerSeries.map (IsLocalRing.residue O) c') + (B : ℕ∞) :=
      le_add_self
    rw [ho] at h2
    have h3 : B ≤ l * y := by exact_mod_cast h2
    omega

omit hϖ in
theorem padicValNat_choose_le_logb (n i : ℕ) : (padicValNat l (n.choose i) : ℝ) ≤ Real.logb l n := by
  have h1 : padicValNat l (n.choose i) ≤ Nat.log l n := by
    rw [← Nat.factorization_def _ hlp.out]
    exact Nat.factorization_choose_le_log
  calc (padicValNat l (n.choose i) : ℝ) ≤ (Nat.log l n : ℝ) := by exact_mod_cast h1
    _ ≤ Real.logb l n := Real.natLog_le_logb n l

theorem content_p1_pow_X_pow_le_general (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) (he : IsUnit e)
    (hu : IsUnit u) (hp : p1 = C (l : O) * e + u * X ^ l) (y b : ℕ) (hy : 1 ≤ y) (hb : 1 ≤ b) :
    cont ϖ (p1 ^ y) ((X : O⟦X⟧) ^ b) ≠ ⊤ ∧
    ((cont ϖ (p1 ^ y) ((X : O⟦X⟧) ^ b)).toNat : ℝ) ≤
      (IsDiscreteValuationRing.addVal O (l : O)).toNat * max 0 ((b : ℝ) / l - y + 2 + Real.logb l b) := by
  set E := (IsDiscreteValuationRing.addVal O (l : O)).toNat
  have hl2 : 2 ≤ l := hlp.out.two_le
  have hab : l * (b / l) ≤ b := Nat.mul_div_le b l
  have hab2 : b < l * (b / l + 1) := by
    have h1 := Nat.div_add_mod b l
    have h2 := Nat.mod_lt b (by omega : 0 < l)
    rw [mul_add, mul_one]; omega
  generalize b / l = a at hab hab2
  obtain ⟨hg, -⟩ := isDist_p1_pow_wdeg hl hu hp y
  have hm2 := m2 hϖ hg ((X : O⟦X⟧) ^ (l * (a + 1) - b)) ((X : O⟦X⟧) ^ b)
  rw [← pow_add, Nat.sub_add_cancel hab2.le, content_p1_pow_X_pow_eq_iInf hϖ hl hl0 he hu hp (a + 1) y hy] at hm2
  set i0 := min (a + 1) (y - 1) with hi0
  have hmem : i0 ∈ Finset.range (min (a + 1) (y - 1) + 1) := Finset.mem_range.mpr (by omega)
  have hle := hm2.trans (iInf₂_le i0 hmem)
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle, ?_⟩
  have hnat := ENat.toNat_le_of_le_natCast hle
  refine (Nat.cast_le.mpr hnat).trans ?_
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  by_cases hcase : a + 1 ≤ y - 1
  · have : i0 = a + 1 := by omega
    rw [this, Nat.sub_self, Nat.choose_self, padicValNat_one_right]
    simp
  · have hi : i0 = y - 1 := by omega
    refine le_trans ?_ (le_max_right _ _)
    have hv := padicValNat_choose_le_logb (l := l) (a + 1) i0
    have hlog : Real.logb l ((a + 1 : ℕ) : ℝ) ≤ Real.logb l b := by
      apply Real.logb_le_logb_of_le (by exact_mod_cast hlp.out.one_lt) (by positivity)
      have : a + 1 ≤ b := by
        have : 2 * a ≤ l * a := Nat.mul_le_mul_right a hl2
        omega
      exact_mod_cast this
    have hsub : ((a + 1 - i0 : ℕ) : ℝ) = (a : ℝ) + 2 - y := by
      rw [Nat.cast_sub (by omega)]
      have : (i0 : ℝ) + 1 = y := by exact_mod_cast (show i0 + 1 = y by omega)
      push_cast; linarith
    have hal : (a : ℝ) ≤ b / l := by
      rw [le_div_iff₀ (by positivity)]
      have : ((l * a : ℕ) : ℝ) ≤ b := by exact_mod_cast hab
      push_cast at this; linarith
    rw [hsub]
    push_cast at hv hlog
    linarith

omit hϖ in
theorem p1_pow_eq_sum_image_choose_mul_X_pow (hp : p1 = C (l : O) * e + u * X ^ l) (y : ℕ) :
    p1 ^ y = ∑ j ∈ (Finset.range (y + 1)).image (l * ·),
      (u ^ (j / l) * e ^ (y - j / l)) * C ((y.choose (j / l) : O) * (l : O) ^ (y - j / l)) * (X : O⟦X⟧) ^ j := by
  rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hlp.out.pos h), p1_pow_eq_sum_choose_mul_X_pow_l_pow hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Nat.mul_div_cancel_left _ hlp.out.pos, ← pow_mul]

theorem content_X_pow_p1_pow_le (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) (he : IsUnit e)
    (hu : IsUnit u) (hp : p1 = C (l : O) * e + u * X ^ l) (B y : ℕ) (hB : 1 ≤ B) :
    cont ϖ ((X : O⟦X⟧) ^ B) (p1 ^ y) ≠ ⊤ ∧
    ((cont ϖ ((X : O⟦X⟧) ^ B) (p1 ^ y)).toNat : ℝ) ≤
      (IsDiscreteValuationRing.addVal O (l : O)).toNat * max 0 ((y : ℝ) - B / l + 2 + Real.logb l y) := by
  set E := (IsDiscreteValuationRing.addVal O (l : O)).toNat
  have hlpos : 0 < l := hlp.out.pos
  obtain ⟨hX, hD⟩ := dist_X_pow (O := O) 1
  rw [pow_one] at hX hD
  have key := Mprime_cont hϖ hX (by rw [hD]) ((Finset.range (y + 1)).image (l * ·))
    (fun j => u ^ (j / l) * e ^ (y - j / l))
    (fun j _ => (hu.pow _).mul (he.pow _))
    (fun j => (y.choose (j / l) : O) * (l : O) ^ (y - j / l))
    (fun j hj => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      rw [Nat.mul_div_cancel_left i hlpos]
      exact coef_ne_zero hl hl0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) B
  rw [p1_pow_eq_sum_image_choose_mul_X_pow hp y, key]
  set i0 := min y ((B - 1) / l) with hi0
  have hq : l * ((B - 1) / l) ≤ B - 1 := Nat.mul_div_le (B - 1) l
  have hq2 : B ≤ l * ((B - 1) / l + 1) := by
    have h1 := Nat.div_add_mod (B - 1) l
    have h2 := Nat.mod_lt (B - 1) hlpos
    rw [mul_add, mul_one]; omega
  have hmem : l * i0 ∈ ((Finset.range (y + 1)).image (l * ·)).filter (· < B) := by
    rw [Finset.mem_filter, Finset.mem_image]
    refine ⟨⟨i0, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
    have : l * i0 ≤ l * ((B - 1) / l) := Nat.mul_le_mul_left l (min_le_right _ _)
    omega
  have hle := iInf₂_le (f := fun j (_ : j ∈ ((Finset.range (y + 1)).image (l * ·)).filter (· < B)) =>
    IsDiscreteValuationRing.addVal O ((y.choose (j / l) : O) * (l : O) ^ (y - j / l))) (l * i0) hmem
  simp only [Nat.mul_div_cancel_left i0 hlpos] at hle
  have hi0y : i0 ≤ y := by omega
  rw [addVal_coef hl hl0 hi0y] at hle
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle, ?_⟩
  have hnat := ENat.toNat_le_of_le_natCast hle
  refine (Nat.cast_le.mpr hnat).trans ?_
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  by_cases hcase : y ≤ (B - 1) / l
  · have : i0 = y := by omega
    rw [this, Nat.sub_self, Nat.choose_self, padicValNat_one_right]
    simp
  · have hi : i0 = (B - 1) / l := by omega
    refine le_trans ?_ (le_max_right _ _)
    have hv := padicValNat_choose_le_logb (l := l) y i0
    have hsub : ((y - i0 : ℕ) : ℝ) = (y : ℝ) - i0 := by rw [Nat.cast_sub (by omega)]
    have hBl : (B : ℝ) / l ≤ i0 + 1 := by
      rw [div_le_iff₀ (by positivity)]
      have : (B : ℝ) ≤ ((l * ((B - 1) / l + 1) : ℕ) : ℝ) := by exact_mod_cast hq2
      rw [← hi] at this
      push_cast at this; linarith
    push_cast [hsub]
    linarith

end P1

end ContPA

end Formalism.MainNotions.N.FrobeniusPowerSeries
