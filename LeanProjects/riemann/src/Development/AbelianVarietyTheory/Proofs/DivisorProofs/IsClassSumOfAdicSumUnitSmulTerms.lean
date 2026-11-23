import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsUnitTermZero

open IsLocalRing GlobalTheory.Poinc GlobalTheory.UT

namespace GlobalTheory.Poinc

theorem isClassSum_of_sumI : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (y : Φ.Y) (N : ℕ), 1 ≤ N → ∀ (κ : Fin s → Φ.X y) (c : Φ.Q) (V' : Type) [CommRing V'] [IsLocalRing V'] (io : Φ.V y →+* V') (e : V'ˣ) (x : V'), SumI (maximalIdeal V') (fun nu : Fin s → Φ.X y => (e : V') * io (Φ.term y (κ + N • nu) c)) x → Φ.IsClassSum y N κ c io (((e⁻¹ : V'ˣ) : V') * x) := by
  intro O _ bar q s W A _ _ Φ y N hN κ c V' _ _ io e x hx j
  classical
  have hinj : Function.Injective (fun nu : Fin s → Φ.X y => κ + N • nu) := by
    intro a b h
    have h1 : N • a = N • b := add_left_cancel h
    funext v
    have h2 : (N : ℤ) • a v = (N : ℤ) • b v := by
      rw [natCast_zsmul, natCast_zsmul]; exact congrFun h1 v
    exact smul_right_injective (Φ.X y) (by omega : (N : ℤ) ≠ 0) h2
  obtain ⟨N', -, -, -, hx⟩ := hx
  obtain ⟨S₀, hS₀⟩ := hx j
  have hF : ((fun nu : Fin s → Φ.X y => κ + N • nu) ⁻¹'
      {mu | True ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ)}).Finite :=
    (PreModel.low_finite Φ y (fun _ => True) j).preimage hinj.injOn
  refine ⟨(S₀ ∪ hF.toFinset).image (fun nu => κ + N • nu), ?_, ?_, ?_⟩
  · intro mu hmu v
    obtain ⟨nu, -, rfl⟩ := Finset.mem_image.1 hmu
    exact ⟨nu v, rfl⟩
  · intro mu hmu hn
    choose nu hnu using hmu
    have e1 : mu = κ + N • nu := funext hnu
    by_contra hlt
    refine hn (Finset.mem_image.2 ⟨nu, Finset.mem_union_right _ ?_, e1.symm⟩)
    rw [Set.Finite.mem_toFinset]
    exact ⟨trivial, by show ∑ i, qW W (Φ.δ y i) (κ + N • nu) < _; rw [← e1]; omega⟩
  · have h := Submodule.smul_mono le_rfl (le_top : N' ≤ ⊤) (hS₀ (S₀ ∪ hF.toFinset) Finset.subset_union_left)
    rw [smul_eq_mul, Ideal.mul_top, ← Finset.mul_sum] at h
    rw [Finset.sum_image hinj.injOn, map_sum]
    have h' := Ideal.mul_mem_left _ ((e⁻¹ : V'ˣ) : V') h
    rwa [mul_sub, Units.inv_mul_cancel_left] at h'

end GlobalTheory.Poinc
