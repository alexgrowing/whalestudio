import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

open Polynomial

namespace GlobalTheory.RootOfUniformiserDVR

theorem val_term_le_one' {F : Type} [Field F] {O : ValuationSubring F} {β : Type} (s : Finset β) (f : β → F)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → O.valuation (f i) = O.valuation (f j) → i = j)
    (hs : O.valuation (∑ i ∈ s, f i) ≤ 1) : ∀ i ∈ s, O.valuation (f i) ≤ 1 := by
  classical
  intro i hi
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => O.valuation (f i)) ⟨i, hi⟩
  by_cases h0 : f j = 0
  · refine (hmax i hi).trans ?_
    simp [h0]
  refine (hmax i hi).trans ?_
  rw [← Finset.add_sum_erase s f hj] at hs
  rwa [Valuation.map_add_eq_of_lt_left] at hs
  refine Valuation.map_sum_lt _ (by simpa using h0) fun k hk => ?_
  rw [Finset.mem_erase] at hk
  exact lt_of_le_of_ne (hmax k hk.2) fun he => hk.1 (hf j hj k hk.2 h0 he.symm).symm

theorem cong_on_adjoin : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] [Algebra W F] [IsScalarTower W (FractionRing W) F]
    (O : ValuationSubring F),
    (∀ w : W, algebraMap W F w ∈ O) → (∀ w ∈ maximalIdeal W, algebraMap W F w ∈ O.nonunits) →
    ∀ (ϖ : W), Irreducible ϖ → ∀ (l : ℕ), l ≠ 0 → ∀ (x : F), x ^ l = algebraMap W F ϖ →
    ∀ (g : F ≃ₐ[FractionRing W] F) (b : F), b ∈ IntermediateField.adjoin (FractionRing W) {x} →
    O.valuation b ≤ 1 → O.valuation (g b - b) < 1 := by
  intro W _ _ _ F _ _ _ _ O hO hm ϖ hϖ l hl0 x hx g b hb hb1
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  set ϖK : FractionRing W := algebraMap W (FractionRing W) ϖ with hϖK
  have hx' : x ^ l = algebraMap (FractionRing W) F ϖK := by
    rw [hx, hϖK, ← IsScalarTower.algebraMap_apply]
  have hunit : ∀ u : Wˣ, O.valuation (algebraMap W F (u : W)) = 1 := by
    intro u
    have a1 := (O.valuation_le_one_iff _).2 (hO u)
    have a2 := (O.valuation_le_one_iff _).2 (hO ((u⁻¹ : Wˣ) : W))
    have e : O.valuation (algebraMap W F (u : W)) * O.valuation (algebraMap W F ((u⁻¹ : Wˣ) : W)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm a1 ?_
    by_contra hc
    push_neg at hc
    have := mul_lt_one_of_lt_of_le hc a2
    rw [e] at this
    exact lt_irrefl _ this
  have hϖlt : O.valuation (algebraMap W F ϖ) < 1 := by
    have := hm ϖ ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
    exact this
  have hWv : ∀ w : W, w ≠ 0 → ∃ n : ℕ,
      O.valuation (algebraMap W F w) = O.valuation (algebraMap W F ϖ) ^ n := by
    intro w hw
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ
    exact ⟨n, by rw [map_mul, map_mul, hunit, _root_.one_mul, map_pow, map_pow]⟩

  have hvpos : ∀ w : W, w ≠ 0 → O.valuation (algebraMap W F w) ≠ 0 := by
    intro w hw
    rw [Valuation.ne_zero_iff]
    intro h0
    apply hw
    have : algebraMap W (FractionRing W) w = 0 := by
      rw [IsScalarTower.algebraMap_apply W (FractionRing W) F] at h0
      exact (map_eq_zero _).mp h0
    exact (IsFractionRing.injective W (FractionRing W)) (by rw [this, map_zero])
  have hK : ∀ a : FractionRing W, a ≠ 0 → ∃ m : ℤ,
      O.valuation (algebraMap (FractionRing W) F a) = O.valuation (algebraMap (FractionRing W) F ϖK) ^ m := by
    intro a ha
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := W) a
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hp0 : p ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨n, hn⟩ := hWv p hp0
    obtain ⟨k, hk⟩ := hWv q hq0
    refine ⟨(n : ℤ) - k, ?_⟩
    rw [map_div₀, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hϖK,
      ← IsScalarTower.algebraMap_apply, hn, hk, zpow_sub₀ (hvpos ϖ hϖ0), zpow_natCast, zpow_natCast]
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0, eq_comm] at hx
    exact hvpos ϖ hϖ0 (by rw [hx, map_zero])
  set t := O.valuation x with ht
  have htl : O.valuation (algebraMap (FractionRing W) F ϖK) = t ^ l := by rw [← hx', map_pow]
  have ht0 : 0 < t := zero_lt_iff.mpr (by simpa [ht] using hx0)
  have ht1 : t < 1 := by
    have := hϖlt
    rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, ← hϖK, htl] at this
    exact (pow_lt_one_iff hl0).mp this
  have hinj : Function.Injective fun n : ℤ => t ^ n := zpow_right_injective₀ ht0 ht1.ne
  have hval : ∀ (a : FractionRing W) (i : ℕ), algebraMap (FractionRing W) F a * x ^ i ≠ 0 →
      ∃ m : ℤ, O.valuation (algebraMap (FractionRing W) F a * x ^ i) = t ^ ((i : ℤ) + l * m) := by
    intro a i ha
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨m, hm⟩ := hK a ha0
    refine ⟨m, ?_⟩
    rw [map_mul, hm, htl, map_pow, zpow_add₀ ht0.ne', zpow_mul, zpow_natCast, zpow_natCast, mul_comm]
  have hmod : ∀ (i j : ℕ) (m n : ℤ), i < l → j < l → t ^ ((i : ℤ) + l * m) = t ^ ((j : ℤ) + l * n) →
      i = j := by
    intro i j m n hi hj he
    have := congrArg (· % (l : ℤ)) (hinj he)
    simp only [Int.add_mul_emod_self_left] at this
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at this
    omega
  have hq : (X ^ l - C ϖK).Monic := monic_X_pow_sub_C _ hl0
  have hint : IsIntegral (FractionRing W) x := ⟨X ^ l - C ϖK, hq, by simp [hx']⟩
  have hb' : b ∈ Algebra.adjoin (FractionRing W) {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]; exact hb
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb'
  obtain ⟨p₀, rfl⟩ := hb'
  set p := p₀ %ₘ (X ^ l - C ϖK)
  have hp : aeval x p = aeval x p₀ := aeval_modByMonic_eq_self_of_root (by simp [hx'])
  have hdeg : p.natDegree < l := by
    have := natDegree_modByMonic_lt p₀ hq (by
      intro h1
      have := congrArg natDegree h1
      rw [natDegree_X_pow_sub_C, natDegree_one] at this
      exact hl0 this)
    rwa [natDegree_X_pow_sub_C] at this
  change O.valuation (aeval x p₀) ≤ 1 at hb1
  change O.valuation (g (aeval x p₀) - aeval x p₀) < 1
  rw [← hp, aeval_eq_sum_range' hdeg] at hb1 ⊢
  simp only [Algebra.smul_def] at hb1 ⊢
  have hle := val_term_le_one' _ _ (fun i hi j hj h0 he => by
    obtain ⟨m, hm⟩ := hval _ i h0
    obtain ⟨n, hn⟩ := hval (p.coeff j) j (by
      intro h00
      rw [h00, map_zero] at he
      exact h0 (by simpa using he))
    exact hmod i j m n (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by rw [← hm, ← hn, he])) hb1
  have hgx : O.valuation (g x) = t := by
    refine pow_left_injective hl0 ?_
    show _ ^ l = t ^ l
    rw [← map_pow, ← map_pow, hx', g.commutes, htl]
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  have hlt : O.valuation (algebraMap (FractionRing W) F (p.coeff i) * x ^ i) < 1 := by
    refine lt_of_le_of_ne (hle i hi) fun he => ?_
    obtain ⟨m, hm⟩ := hval (p.coeff i) i (by intro h0; simp [h0] at he)
    have := hmod i 0 m 0 (Finset.mem_range.mp hi) (by omega) (by rw [← hm, he]; simp)
    omega
  refine Valuation.map_sub_lt _ ?_ hlt
  rw [map_mul g, g.commutes, map_pow g, map_mul, map_pow, hgx]
  rwa [map_mul, map_pow] at hlt

end GlobalTheory.RootOfUniformiserDVR
