import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Shift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω}

omit [Fintype K] in

theorem shift_succ_sub_one (b : K → ℤ) (j : ℕ) :
    (b + fun _ => ((j + 1 : ℕ) : ℤ)) - 1 = b + fun _ => (j : ℤ) := by
  funext k
  simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply]
  push_cast
  ring

omit [∀ k, Fintype (ι k)] in

theorem pow_mul_mem_chartLatQ (c : ∀ k, ι k) (b : K → ℤ) {s : Ω} (hs : s ∈ chartLatQ y b 1) (j : ℕ) :
    (∏ k, y ⟨k, c k⟩) ^ j * s ∈ chartLatQ y (b + fun _ => (j : ℤ)) 1 := by
  induction j with
  | zero =>
    rw [pow_zero, one_mul]
    convert hs using 2
    funext k
    simp
  | succ j ih =>
    rw [← shift_succ_sub_one] at ih
    have h := mul_mem_chartLatQ (c := c) (b + fun _ => ((j + 1 : ℕ) : ℤ)) ih
    rwa [← mul_assoc, ← pow_succ'] at h

theorem finiteDimensional_chartLatQ (hfin : SectionLatticeFinite.Statement) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (b : K → ℤ) : FiniteDimensional ℚ (chartLatQ y b 1) := by
  obtain ⟨S, hS⟩ := hfin K ι Ω y b 1 hy
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ (S : Set Ω)) fun s hs => ?_
  obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y b 1 s hs
  rw [← hS] at hNs
  have hZ : (N : Ω) * s ∈ Submodule.span ℤ (S : Set Ω) :=
    (AddSubgroup.closure_le (K := (Submodule.span ℤ (S : Set Ω)).toAddSubgroup)).mpr
      Submodule.subset_span hNs
  have hQ : (N : Ω) * s ∈ Submodule.span ℚ (S : Set Ω) := Submodule.span_le_restrictScalars ℤ ℚ _ hZ
  have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
    rw [Rat.smul_def]
    push_cast
    field_simp
  rw [hs']
  exact Submodule.smul_mem _ _ hQ

theorem finrank_shift_le (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) (j : ℕ) :
    Module.finrank ℚ (chartLatQ y (b + fun _ => (j : ℤ)) 1) ≤ Module.finrank ℚ (chartLatQ y b 1) +
      ∑ i ∈ Finset.range j, Module.finrank ℚ (chartLatQ y (b + fun _ => ((i + 1 : ℕ) : ℤ)) 1 ⧸
        chartDivSec y c (b + fun _ => ((i + 1 : ℕ) : ℤ))) := by
  induction j with
  | zero =>
    have h0 : (b + fun _ => ((0 : ℕ) : ℤ)) = b := by funext k; simp
    rw [h0]
    simp
  | succ j ih =>
    have h := finrank_chartLatQ_le hc (b + fun _ => ((j + 1 : ℕ) : ℤ))
    rw [shift_succ_sub_one] at h
    rw [Finset.sum_range_succ]
    omega

end Shift

theorem ShiftSectionBound.proof (hfin : SectionLatticeFinite.Statement) (hQ : ShiftQuotientBound.Statement) :
    ShiftSectionBound.Statement := by
  intro K _ ι _ Ω _ _ y D a m hD hV hB
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker]
    simp [mConeMap, h0]
  choose c hc using hy
  have hC := fun i : ℕ => hQ K ι Ω y D a (fun _ => ((i + 1 : ℕ) : ℤ)) c hD hV hB hc
  choose C hC using hC
  refine ⟨∑ i ∈ Finset.range m, C i,
    ((Filter.eventually_all_finset (Finset.range m)).mpr fun i _ => hC i).mono fun n hn => ⟨?_, ?_⟩⟩
  ·
    have := finiteDimensional_chartLatQ hfin (fun k => ⟨c k, hc k⟩) ((n : ℤ) • a + fun _ => (m : ℤ))
    have hh : (∏ k, y ⟨k, c k⟩) ^ m ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k _ => hc k)
    let φ : chartLatQ y ((n : ℤ) • a) 1 →ₗ[ℚ] chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1 :=
      { toFun := fun s => ⟨(∏ k, y ⟨k, c k⟩) ^ m * s, pow_mul_mem_chartLatQ c _ s.2 m⟩
        map_add' := fun s t => Subtype.ext (mul_add _ _ _)
        map_smul' := fun r s => Subtype.ext (mul_smul_comm r _ (s : Ω)) }
    have hinj : Function.Injective φ := fun s t hst =>
      Subtype.ext (mul_left_cancel₀ hh (congrArg Subtype.val hst))
    exact_mod_cast LinearMap.finrank_le_finrank_of_injective hinj
  · have h := finrank_shift_le c hc ((n : ℤ) • a) m
    have h' : (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ≤
        (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) +
          ∑ i ∈ Finset.range m, (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ)) 1 ⧸
            chartDivSec y c ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ))) : ℝ) := by
      exact_mod_cast h
    have hs : ∑ i ∈ Finset.range m, (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ)) 1 ⧸
          chartDivSec y c ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ))) : ℝ) ≤
        (∑ i ∈ Finset.range m, C i) * (n : ℝ) ^ (D - 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => hn i hi
    linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
