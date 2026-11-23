import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFieldCmCurvesUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPComplexMultiplicationCongruenceModPrStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPTorsionIntegralAndDistinctModStatement

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.WeberCongruence

theorem mem_of_isIntegral (W : ValuationSubring ℂ) {x : ℂ} (hx : IsIntegral ℤ x) : x ∈ W := by
  have h1 : IsIntegral W x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  exact y.2

theorem mem_of_pow_mem (W : ValuationSubring ℂ) {x : ℂ} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n ∈ W) :
    x ∈ W := by
  rw [← W.valuation_le_one_iff] at hx ⊢
  rw [map_pow] at hx
  exact (pow_le_one_iff_of_nonneg zero_le hn).mp hx

theorem mul_mem_nonunits (W : ValuationSubring ℂ) {x y : ℂ} (hx : x ∈ W.nonunits) (hy : y ∈ W) :
    x * y ∈ W.nonunits := by
  rw [W.mem_nonunits_iff] at hx ⊢
  rw [← W.valuation_le_one_iff] at hy
  rw [map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hx hy

theorem mem_nonunits_of_mul (W : ValuationSubring ℂ) {x y : ℂ} (hx : x ∉ W.nonunits)
    (h : x * y ∈ W.nonunits) : y ∈ W.nonunits := by
  rw [W.mem_nonunits_iff] at hx h ⊢
  rw [map_mul] at h
  by_contra hy
  exact absurd h (not_lt.mpr (one_le_mul_of_one_le_of_one_le (not_lt.mp hx) (not_lt.mp hy)))

theorem sub_mem_nonunits_iff (W : ValuationSubring ℂ) (x y : W) :
    (x : ℂ) - y ∈ W.nonunits ↔ IsLocalRing.residue W x = IsLocalRing.residue W y := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem charP_residueField (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime)
    (h : (p : ℂ) ∈ W.nonunits) : CharP (IsLocalRing.ResidueField W) p := by
  rw [CharP.charP_iff_prime_eq_zero hp]
  have := (sub_mem_nonunits_iff W (p : W) 0).mp (by simpa using h)
  simpa using this

theorem inv_natCast_mem (W : ValuationSubring ℂ) {p m : ℕ} (hp : p.Prime)
    (h : (p : ℂ) ∈ W.nonunits) (hm : ¬ p ∣ m) : (m : ℂ)⁻¹ ∈ W := by
  have := charP_residueField W hp h
  have h1 : (m : ℂ) ∉ W.nonunits := fun hc ↦ by
    have := (sub_mem_nonunits_iff W (m : W) 0).mp (by simpa using hc)
    rw [map_natCast, map_zero, CharP.cast_eq_zero_iff _ p] at this
    exact hm this
  rw [ValuationSubring.mem_nonunits_iff_or] at h1
  push Not at h1
  exact h1.2

theorem pow_six_eq_one {k : Type*} [CommRing k] {p : ℕ} (hp : p.Prime) [CharP k p] {g h a : k}
    (e : g ^ 3 - 27 * h ^ 2 = 1) (h2 : g = a ^ 2 * g ^ p) (h3 : h = a ^ 3 * h ^ p) :
    a ^ 6 = 1 := by
  have := Fact.mk hp
  have e1 := congrArg (frobenius k p) e
  simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, frobenius_def] at e1
  generalize g ^ p = G at *
  generalize h ^ p = H at *
  subst h2 h3
  linear_combination e - a ^ 6 * e1

theorem congruences (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    {g h a : ℂ} (hg : g ∈ W) (hh : h ∈ W) (ha : a ∈ W) (e : g ^ 3 - 27 * h ^ 2 = 1)
    (h2 : g - a ^ 2 * g ^ p ∈ W.nonunits) (h3 : h - a ^ 3 * h ^ p ∈ W.nonunits) :
    g ^ 3 - (g ^ 3) ^ p ∈ W.nonunits ∧ ∀ x y, x ∈ W → y - a * x ^ p ∈ W.nonunits →
      g * h * y - (g * h * x) ^ p ∈ W.nonunits := by
  have := charP_residueField W hp hW
  lift g to W using hg
  lift h to W using hh
  lift a to W using ha
  have e' : g ^ 3 - 27 * h ^ 2 = 1 := Subtype.ext e
  have e1 := congrArg (IsLocalRing.residue W) e'
  have e2 := (sub_mem_nonunits_iff W g (a ^ 2 * g ^ p)).mp h2
  have e3 := (sub_mem_nonunits_iff W h (a ^ 3 * h ^ p)).mp h3
  simp only [map_sub, map_mul, map_pow, map_one, map_ofNat] at e1 e2 e3
  have e4 := pow_six_eq_one hp e1 e2 e3
  refine ⟨(sub_mem_nonunits_iff W (g ^ 3) ((g ^ 3) ^ p)).mpr ?_, fun x y hx hy ↦ ?_⟩
  · simp only [map_pow]
    rw [← pow_mul _ 3 p, mul_comm 3 p, pow_mul]
    generalize IsLocalRing.residue W g ^ p = G at *
    rw [e2]
    linear_combination G ^ 3 * e4
  · lift x to W using hx
    have hy' : y ∈ W := by
      have := add_mem (W.nonunits_subset hy) (a * x ^ p).2
      simpa using this
    lift y to W using hy'
    have e5 := (sub_mem_nonunits_iff W y (a * x ^ p)).mp hy
    refine (sub_mem_nonunits_iff W (g * h * y) ((g * h * x) ^ p)).mpr ?_
    simp only [map_mul, map_pow, mul_pow] at e5 ⊢
    generalize IsLocalRing.residue W g ^ p = G at *
    generalize IsLocalRing.residue W h ^ p = H at *
    rw [e2, e3, e5]
    linear_combination G * H * IsLocalRing.residue W x ^ p * e4

theorem norm_sq_eq_absNorm {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (π : 𝓞 K) :
    ‖σ π‖ ^ 2 = Ideal.absNorm (Ideal.span {π}) := by
  have h1 : Fintype.card (InfinitePlace K) = 1 := by
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h3 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h4 := IsTotallyComplex.nrRealPlaces_eq_zero K
    omega
  have : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp h1.le
  have h5 := InfinitePlace.prod_eq_abs_norm (π : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk σ), IsTotallyComplex.mult_eq,
    InfinitePlace.apply] at h5
  rw [h5, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp

theorem weber_congruences : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ (W : ValuationSubring ℂ) (π : 𝓞 K) (p : ℕ), p.Prime → 5 ≤ p → Ideal.absNorm (Ideal.span {π}) = p → ((π : K) : ℂ) ∈ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∈ W ∧ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ^ p ∈ W.nonunits ∧ ∀ (m : ℕ), Odd m → ¬ p ∣ m → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ∈ W ∧ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (((π : K) : ℂ) * t)) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ^ p ∈ W.nonunits) ∧ ((L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∉ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - 1 ∉ W.nonunits → ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice) := by
  intro K _ _ hK L hL W π p hp h5 hN hπ
  have hcm : ∀ a : 𝓞 K, ∀ z ∈ L.lattice, ((a : K) : ℂ) * z ∈ L.lattice := fun a z hz ↦ by
    obtain ⟨b, rfl⟩ := (hL z).mp hz
    exact (hL _).mpr ⟨a * b, by simp⟩
  have hj := mem_of_isIntegral W
    (CMCurves.isIntegral_latticeJ hK (K.val : K →+* ℂ) L hcm)
  have hn : ‖((π : K) : ℂ)‖ ^ 2 = p := by
    rw [← hN]; exact norm_sq_eq_absNorm hK (K.val : K →+* ℂ) π
  have hπi : IsIntegral ℤ ((π : K) : ℂ) :=
    (RingOfIntegers.isIntegral_coe π).map (K.val : K →+* ℂ).toIntAlgHom
  have hpW : (p : ℂ) ∈ W.nonunits := by
    have := mul_mem_nonunits W hπ
      (mem_of_isIntegral W (hπi.map (starRingEnd ℂ).toIntAlgHom))
    convert this using 1
    change _ = _ * (starRingEnd ℂ) _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    simp
  have i2 : (2 : ℂ)⁻¹ ∈ W := by
    simpa using inv_natCast_mem W (m := 2) hp hpW fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h; omega
  have i3 : (3 : ℂ)⁻¹ ∈ W := by
    simpa using inv_natCast_mem W (m := 3) hp hpW fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h; omega
  have hΔ := g₂_cube_sub_g₃_sq_ne_zero L
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (n := 12) (by norm_num)
  have hc0 : c ≠ 0 := by rintro rfl; exact hΔ (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  generalize scalePeriods L c hc0 = L' at H
  have hΔ' : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = 1 := by
    rw [H.g₂_eq, H.g₃_eq]; field_simp; linear_combination -hc
  have eJ : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = L'.g₂ ^ 3 := by
    rw [H.g₂_eq, ← hc]; field_simp
  have eW : ∀ t, L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t =
      L'.g₂ * L'.g₃ * L'.weierstrassP (c * t) := fun t ↦ by
    rw [H.g₂_eq, H.g₃_eq, H.weierstrassP_mul, ← hc]; field_simp
  have hJ : L'.g₂ ^ 3 ∈ W := by
    have := mul_mem (mul_mem (pow_mem i2 6) (pow_mem i3 3)) hj
    convert this using 1
    rw [← eJ, CMCurves.latticeJ]; ring
  have hg := mem_of_pow_mem W three_ne_zero hJ
  have hh : L'.g₃ ∈ W := by
    refine mem_of_pow_mem W two_ne_zero ?_
    have := mul_mem (pow_mem i3 3) (sub_mem hJ (one_mem W))
    convert this using 1
    linear_combination (-1 / 27 : ℂ) * hΔ'
  have hD : (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)⁻¹ ∈ W := by rw [hΔ', inv_one]; exact one_mem W
  obtain ⟨a, ha, -, -, a2, a3, a4⟩ := GlobalTheory.T.weierstrassP_complexMultiplication_congruence_mod_prime L' W ((π : K) : ℂ) p i2 i3 hg hh hD hp hpW hπ
    (fun l hl ↦ by
      obtain ⟨z, rfl⟩ : ∃ z, l = c * z := ⟨c⁻¹ * l, by field_simp⟩
      rw [mul_left_comm]
      exact (H _).mpr (hcm π z ((H z).mp hl))) hn
  obtain ⟨c1, c2⟩ := congruences W hp hpW hg hh ha hΔ' a2 a3
  simp only [eW]
  rw [eJ]
  refine ⟨hJ, c1, fun m hm hpm ↦ ?_⟩
  have im := inv_natCast_mem W hp hpW hpm
  obtain ⟨t1, t2⟩ := GlobalTheory.T.weierstrassP_torsion_integral_and_distinct_mod L' W m i2 i3 hg hh hD hm im
  have s1 : ∀ t, (m : ℂ) * t ∈ L.lattice → (m : ℂ) * (c * t) ∈ L'.lattice := fun t ht ↦ by
    rw [mul_left_comm]; exact (H _).mpr ht
  refine ⟨fun t ht ht' ↦ ?_, fun n1 n2 t t' ht ht0 ht' ht0' h ↦ ?_⟩
  · have hx := t1 (c * t) (s1 t ht) ((H t).not.mpr ht')
    refine ⟨mul_mem (mul_mem hg hh) hx, c2 _ _ hx ?_⟩
    rw [mul_left_comm]
    exact a4 m (c * t) hm im (s1 t ht) ((H t).not.mpr ht')
  · have n3 : L'.g₂ ∉ W.nonunits := fun h ↦ n1 (by
      simpa [pow_succ'] using mul_mem_nonunits W h (pow_mem hg 2))
    have n4 : L'.g₃ ∉ W.nonunits := fun h ↦ n2 (by
      have := mul_mem_nonunits W h (mul_mem (ofNat_mem W 27) hh)
      convert this using 1
      linear_combination hΔ')
    rw [← mul_sub, mul_assoc] at h
    have := t2 (c * t) (c * t') (s1 t ht) ((H t).not.mpr ht0) (s1 t' ht') ((H t').not.mpr ht0')
      (mem_nonunits_of_mul W n4 (mem_nonunits_of_mul W n3 h))
    rwa [← mul_sub, ← mul_add, H, H] at this

end GlobalTheory.WeberCongruence
