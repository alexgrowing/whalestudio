import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeEsymmScaledMultisetAddSegment
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHecke.StringEig

open GlobalTheory.ChainOnto (esymm_add_C esymm_map_mul_C esymm_string esymm_eq_zero_of_lt sqrt_sq_C natCast_cpow_half)

theorem map_coe_segL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (z : ℂˣ) (t : ℕ) :
    (segL ϖ z t).map (fun b : ℂˣ => (b : ℂ)) =
      (Finset.range t).val.map fun i : ℕ => (z : ℂ) * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ ((t : ℤ) - 1 - 2 * i) := by
  rw [segL, Multiset.map_map, Finset.range_val]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Units.val_mul]
  congr 1
  rw [GlobalTheory.MellinPoly.absPow_eq_zpow, ord_eq_one hϖ, zpow_one, ← natCast_cpow_half]
  congr 1
  push_cast
  ring

theorem genVal_add_segL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r N t n₀ : ℕ) (B : Multiset ℂˣ) (zS zT : ℂˣ), B.card = N → n₀ ≤ N + t → genVal (resCard k) r (N + t) (B.map (· * (zS * zT⁻¹)) + segL ϖ zS t) n₀ = (zS : ℂ) ^ n₀ * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n₀ * (r + N)) * ∑ n ∈ Finset.range (N + 1), (if n ≤ n₀ then ((resCard k ^ (n * (t - (n₀ - n))) * Formalism.L2.Col.gaussBin (resCard k) t (n₀ - n) : ℕ) : ℂ) else 0) * (((zT : ℂ) ^ n * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n * (r + N + t)))⁻¹ * genVal (resCard k) r N B n) := by
  intro k _ _ _ _ ϖ hϖ r N t n₀ B zS zT hB hn₀
  set Q := resCard k with hQdef
  have hsQ := sqrt_sq_C Q
  have hs : ((Real.sqrt Q : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hsQ
    have h1 : 1 < Q := one_lt_resCard k
    have : ((Q : ℕ) : ℂ) = 0 := by rw [← hsQ]; ring
    exact (by omega : Q ≠ 0) (by exact_mod_cast this)
  set s : ℂ := ((Real.sqrt Q : ℝ) : ℂ) with hsdef
  have hA : (B.map (· * (zS * zT⁻¹))).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map fun b : ℂˣ => (b : ℂ)).map fun x => ((zS : ℂ) * (zT : ℂ)⁻¹) * x := by
    simp [Multiset.map_map, Function.comp_def, mul_comm]
  have hBc : (B.map fun b : ℂˣ => (b : ℂ)).card = N := by simp [hB]
  set F : ℕ → ℂ := fun n => (if n ≤ n₀ then ((Q ^ (n * (t - (n₀ - n))) * Formalism.L2.Col.gaussBin Q t (n₀ - n) : ℕ) : ℂ) else 0) *
    (((zT : ℂ) ^ n * s ^ (n * (r + N + t)))⁻¹ * genVal Q r N B n) with hF
  have hFa : ∀ j, N < j → F j = 0 := by
    intro j hj
    simp only [hF, genVal, esymm_eq_zero_of_lt _ (hBc ▸ hj), mul_zero]
  have hFk : ∀ j, n₀ < j → F j = 0 := by
    intro j hj
    simp only [hF, if_neg (show ¬ j ≤ n₀ by omega), zero_mul]
  have hR : ∑ j ∈ Finset.range (N + 1), F j = ∑ j ∈ Finset.range (n₀ + 1), F j := by
    rw [Finset.sum_subset (Finset.range_mono (show N + 1 ≤ N + n₀ + 1 by omega))
        (fun j _ hn => hFa j (by simp at hn; omega)),
      Finset.sum_subset (Finset.range_mono (show n₀ + 1 ≤ N + n₀ + 1 by omega))
        (fun j _ hn => hFk j (by simp at hn; omega))]
  rw [hR, genVal, Multiset.map_add, esymm_add_C, Finset.mul_sum, Finset.mul_sum, hA, map_coe_segL k ϖ hϖ]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ n₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [esymm_map_mul_C, esymm_string Q s zS hs hsQ t]
  simp only [hF, if_pos hjk, genVal]
  by_cases hjN : j ≤ N
  · by_cases hat : n₀ - j ≤ t
    · have hsI : s ^ (r * n₀ + n₀ * (N + t - n₀)) * s ^ (-(((n₀ - j : ℕ) : ℤ) * ((t : ℤ) - ((n₀ - j : ℕ) : ℤ)))) =
          s ^ (n₀ * (r + N)) * (s ^ 2) ^ (j * (t - (n₀ - j))) * (s ^ (j * (r + N + t)))⁻¹ * s ^ (r * j + j * (N - j)) := by
        rw [← pow_mul]
        simp only [← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ hs]
        congr 1
        push_cast [Nat.cast_sub hjN, Nat.cast_sub hjk, Nat.cast_sub hat, Nat.cast_sub hn₀]
        ring
      have hz : ((zS : ℂ) * (zT : ℂ)⁻¹) ^ j * (zS : ℂ) ^ (n₀ - j) = (zS : ℂ) ^ n₀ * ((zT : ℂ) ^ j)⁻¹ := by
        rw [mul_pow, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hjk, inv_pow]
      calc _ = (s ^ (r * n₀ + n₀ * (N + t - n₀)) * s ^ (-(((n₀ - j : ℕ) : ℤ) * ((t : ℤ) - ((n₀ - j : ℕ) : ℤ))))) *
            (((zS : ℂ) * (zT : ℂ)⁻¹) ^ j * (zS : ℂ) ^ (n₀ - j)) *
            ((Formalism.L2.Col.gaussBin Q t (n₀ - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by ring
        _ = (s ^ (n₀ * (r + N)) * (s ^ 2) ^ (j * (t - (n₀ - j))) * (s ^ (j * (r + N + t)))⁻¹ * s ^ (r * j + j * (N - j))) *
            ((zS : ℂ) ^ n₀ * ((zT : ℂ) ^ j)⁻¹) *
            ((Formalism.L2.Col.gaussBin Q t (n₀ - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by rw [hsI, hz]
        _ = _ := by rw [hsQ]; push_cast; rw [mul_inv]; ring
    · rw [Formalism.L2.Col.gaussBin_eq_zero Q (show t < n₀ - j by omega)]
      simp
  · rw [esymm_eq_zero_of_lt _ (by omega)]
    simp

end GlobalTheory.ParHecke.StringEig

end
