import Mathlib
import Formalism.PeriodIntegrals.StrongApproxE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.LocSmall

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace PI.StrongApproxE

open Formalism.MainNotions.S.Loc

theorem local_dense_embedding : LocDense := by
  intro F E _ _ _ _ _ sig p L V hV α
  have := L.lf
  have ho : IsOpen {x : L.Fp | x - α ∈ V} := hV.preimage (continuous_sub_right α)
  obtain ⟨a, ha⟩ := L.dense.exists_mem_open ho ⟨α, by simp⟩
  exact ⟨a, ha⟩

theorem local_neighbourhood_small : LocSmall := by
  intro F E _ _ _ _ _ sig p L V hV
  have := L.lf
  have hV0 : (V : Set L.Fp) ∈ nhds (0 : L.Fp) := hV.mem_nhds V.zero_mem
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp hV0
  obtain ⟨r, hr⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero L.Fp)
  obtain ⟨r', hr'0, hr'1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation L.Fp)
  set x₀ : L.Fp := r * r' with hx₀
  have hx₀v : valuation L.Fp x₀ < γ := by
    rw [hx₀, map_mul, hr]
    calc (γ : ValueGroupWithZero L.Fp) * valuation L.Fp r'
        < (γ : ValueGroupWithZero L.Fp) * 1 := by
          exact mul_lt_mul_of_pos_left hr'1 (by simp [pos_iff_ne_zero])
      _ = γ := mul_one _
  have hx₀0 : valuation L.Fp x₀ ≠ 0 := by
    rw [hx₀, map_mul, hr]
    exact mul_ne_zero (Units.ne_zero γ) (by simpa using hr'0)
  have hs : {y : L.Fp | valuation L.Fp (y - x₀) < valuation L.Fp x₀} ∈ nhds x₀ :=
    IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ hx₀0, fun y hy => by simpa using hy⟩
  obtain ⟨_, hy, ⟨c, rfl⟩⟩ := mem_closure_iff_nhds.mp (L.dense x₀) _ hs
  have hyv : valuation L.Fp (L.ιF c) = valuation L.Fp x₀ := Valuation.map_eq_of_sub_lt _ hy
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hyv
    exact hx₀0 hyv.symm
  refine ⟨c, hc0, fun z hz => ?_⟩
  have h1 : L.ιF z ≤ᵥ L.ιF c := (L.val z c).mpr hz
  have h2 : valuation L.Fp (L.ιF z) ≤ valuation L.Fp (L.ιF c) :=
    (Valuation.Compatible.vle_iff_le (v := valuation L.Fp) _ _).mp h1
  exact hγ (show valuation L.Fp (L.ιF z) < γ from lt_of_le_of_lt (h2.trans_eq hyv) hx₀v)

theorem local_integral_of_substitution : LocInt := by
  intro F E _ _ _ _ _ sig p L z e hz he
  have := L.lf
  have h1 : L.ιF z ≤ᵥ L.ιF 1 := (L.val z 1).mpr (by simpa using hz)
  have hzO : L.ιF z ∈ 𝒪[L.Fp] := by
    rw [Valuation.mem_integer_iff]
    have := (Valuation.Compatible.vle_iff_le (v := valuation L.Fp) _ _).mp h1
    simpa using this
  have hE : IsIntegral 𝒪[L.Fp] (L.ιE e) := (map_isIntegral_int L.ιE he).tower_top
  have hA : IsIntegral 𝒪[L.Fp] (algebraMap L.Fp L.Ep (L.ιF z)) := by
    have := isIntegral_algebraMap (R := 𝒪[L.Fp]) (A := L.Ep) (x := ⟨L.ιF z, hzO⟩)
    exact this
  rw [Algebra.smul_def]
  exact L.O.mul_mem ((L.O_def _).mpr hA) ((L.O_def _).mpr hE)

end PI.StrongApproxE
