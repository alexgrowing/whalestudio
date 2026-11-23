import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in
theorem one_lt_resCard : 1 < resCard k := Finite.one_lt_card

theorem nabs_le_of_valuation_le {x y : kˣ} (h : valuation k (x : k) ≤ valuation k (y : k)) :
    nabs k x ≤ nabs k y := by
  borelize k
  obtain ⟨ν, hν, h1⟩ := exists_isUnitVol k
  have hx := measureReal_cball ν x
  have hy := measureReal_cball ν y
  have h2 : ν.real (𝒪[k] : Set k) = 1 := by rw [Measure.real, h1]; simp
  rw [h2, mul_one] at hx hy
  rw [← hx, ← hy]
  have h3 : cball x ⊆ cball y := fun z hz => le_trans (show valuation k z ≤ _ from hz) h
  exact measureReal_mono h3 (isCompact_cball y).measure_lt_top.ne

theorem nabs_lt_of_valuation_lt {x y : kˣ} (h : valuation k (x : k) < valuation k (y : k)) :
    nabs k x < nabs k y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  have hy0 : 0 < valuation k (y : k) := by simp [zero_lt_iff]
  have hlt : valuation k ((x : k) * (y : k)⁻¹) < 1 := by
    rw [map_mul, map_inv₀, mul_inv_lt_iff₀ hy0, one_mul]; exact h
  let z : 𝒪[k] := ⟨(x : k) * (y : k)⁻¹, (Valuation.mem_integer_iff _ _).mpr hlt.le⟩
  have hz : z ∈ 𝓂[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hlt
  have h1 : valuation k ((x : k) * (y : k)⁻¹) ≤ valuation k (ϖ : k) :=
    (mem_cball_uniformiser hϖ (x := Units.mk0 _ h0) rfl z).mpr hz
  have h2 : valuation k (x : k) ≤ valuation k ((Units.mk0 _ h0 * y : kˣ) : k) := by
    rw [map_mul, map_inv₀, mul_inv_le_iff₀ hy0] at h1
    rw [Units.val_mul, map_mul]
    exact h1
  have h3 := nabs_le_of_valuation_le h2
  rw [nabs_mul, nabs_uniformiser hϖ (x := Units.mk0 _ h0) rfl] at h3
  refine h3.trans_lt (mul_lt_of_lt_one_left (nabs_pos k y) (inv_lt_one_of_one_lt₀ ?_))
  exact_mod_cast one_lt_resCard k

theorem nabs_le_iff (x y : kˣ) : nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k) :=
  ⟨fun h => not_lt.mp fun h' => absurd h (not_le.mpr (nabs_lt_of_valuation_lt h')),
    nabs_le_of_valuation_le⟩

theorem nabs_eq_iff (x y : kˣ) : nabs k x = nabs k y ↔ valuation k (x : k) = valuation k (y : k) := by
  rw [le_antisymm_iff, le_antisymm_iff, nabs_le_iff, nabs_le_iff]

theorem nabs_eq_one_iff (x : kˣ) : nabs k x = 1 ↔ valuation k (x : k) = 1 := by
  rw [← nabs_one k, nabs_eq_iff, Units.val_one, map_one]

variable (k) in
theorem isLocallyConstant_nabs : IsLocallyConstant (nabs k) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  have h1 : (fun z : kˣ => (z : k) - x) ⁻¹' cball (Units.mk0 r hr0 * x) ∈ 𝓝 x :=
    ((isOpen_cball _).preimage (Units.continuous_val.sub continuous_const)).mem_nhds (by simp [cball])
  filter_upwards [h1] with z hz
  rw [nabs_eq_iff]
  have h2 : valuation k ((z : k) - x) ≤ valuation k (r * x) := hz
  refine Valuation.map_eq_of_sub_lt _ (h2.trans_lt ?_)
  rw [map_mul]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1

theorem nabs_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x y : kˣ, nabs k (x * y) = nabs k x * nabs k y) ∧ (∀ x : kˣ, 0 < nabs k x) ∧ (∀ x y : kˣ, nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k)) ∧ (∀ x : kˣ, nabs k x = 1 ↔ valuation k (x : k) = 1) ∧ (∀ (ϖ : 𝒪[k]) (x : kˣ), Irreducible ϖ → (x : k) = (ϖ : k) → nabs k x = (resCard k : ℝ)⁻¹) ∧ IsLocallyConstant (nabs k) ∧ 1 < resCard k :=
  fun k _ _ _ _ => ⟨nabs_mul k, nabs_pos k, nabs_le_iff, nabs_eq_one_iff,
    fun _ _ h h' => nabs_uniformiser h h', isLocallyConstant_nabs k, one_lt_resCard k⟩

end GlobalTheory.SplitWeil
