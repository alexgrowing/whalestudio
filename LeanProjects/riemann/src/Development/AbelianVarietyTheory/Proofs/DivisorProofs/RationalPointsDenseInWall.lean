import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

theorem wallSet_floor_mem {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (j : ℕ) (τ₀ : ι) (hN : 0 < N) (m : ℕ)
    (hm : 0 < m) (u : ι → Fin N → ℝ) (hu : u ∈ wallSet (N := N) j τ₀ (1 / (4 * (N : ℝ)))) :
    (fun τ i => ((⌊(4 * (N : ℝ) * m) * u τ i⌋ : ℤ) : ℝ) / (4 * (N : ℝ) * m)) ∈
      wallSet (N := N) j τ₀ (1 / (4 * (N : ℝ))) := by
  obtain ⟨h1, h2, h3⟩ := hu
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hM : (0 : ℝ) < 4 * (N : ℝ) * m := by positivity
  refine ⟨fun τ i => ?_, fun a b hab hb => ?_, fun τ a b hab hb => ?_⟩
  · have h := abs_le.mp (h1 τ i)
    have hup : ((⌊(4 * (N : ℝ) * m) * u τ i⌋ : ℤ) : ℝ) ≤ (4 * (N : ℝ) * m) * u τ i := Int.floor_le _
    have hlo : -(2 * (N : ℤ) * m) ≤ ⌊(4 * (N : ℝ) * m) * u τ i⌋ := by
      rw [Int.le_floor]
      push_cast
      nlinarith [h.1]
    have hlo' : -(2 * (N : ℝ) * m) ≤ ((⌊(4 * (N : ℝ) * m) * u τ i⌋ : ℤ) : ℝ) := by exact_mod_cast hlo
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hM]; linarith
    · rw [div_le_iff₀ hM]; nlinarith [h.2]
  · simp only [h2 a b hab hb]
  · have h := h3 τ a b hab hb
    have hk : (4 * (N : ℝ) * m) * u τ b + m ≤ (4 * (N : ℝ) * m) * u τ a := by
      have := mul_le_mul_of_nonneg_left h hM.le
      have e : (4 * (N : ℝ) * m) * (1 / (4 * (N : ℝ))) = m := by field_simp
      rw [e] at this
      linarith
    have hf := Int.floor_le_floor hk
    rw [Int.floor_add_natCast] at hf
    have hf' : ((⌊(4 * (N : ℝ) * m) * u τ b⌋ : ℤ) : ℝ) + m ≤ ((⌊(4 * (N : ℝ) * m) * u τ a⌋ : ℤ) : ℝ) := by
      exact_mod_cast hf
    show 1 / (4 * (N : ℝ)) ≤ _
    rw [← sub_div, le_div_iff₀ hM]
    have e : (1 / (4 * (N : ℝ))) * (4 * (N : ℝ) * m) = m := by field_simp
    rw [e]
    linarith

theorem wallSet_subset_closure_rat : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) (τ₀ : ι), 1 ≤ j → j < N → wallSet (N := N) j τ₀ (1 / (4 * (N : ℝ))) ⊆ closure {u | u ∈ wallSet (N := N) j τ₀ (1 / (4 * (N : ℝ))) ∧ ∀ τ i, ∃ q : ℚ, u τ i = (q : ℝ)} := by
  intro ι _ _ N j τ₀ _ hjN u hu
  have hN : 0 < N := by omega
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm' : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hM : (0 : ℝ) < 4 * (N : ℝ) * ((m + 1 : ℕ) : ℝ) := by positivity
  refine ⟨_, ⟨wallSet_floor_mem j τ₀ hN (m + 1) (Nat.succ_pos m) u hu, fun τ i => ?_⟩, ?_⟩
  · refine ⟨(⌊(4 * (N : ℝ) * ((m + 1 : ℕ) : ℝ)) * u τ i⌋ : ℤ) / (4 * (N : ℚ) * ((m + 1 : ℕ) : ℚ)), ?_⟩
    push_cast
    rfl
  · rw [dist_pi_lt_iff hε]
    intro τ
    rw [dist_pi_lt_iff hε]
    intro i
    have h1 := Int.floor_le ((4 * (N : ℝ) * ((m + 1 : ℕ) : ℝ)) * u τ i)
    have h2 := Int.lt_floor_add_one ((4 * (N : ℝ) * ((m + 1 : ℕ) : ℝ)) * u τ i)
    have h3 : 1 < ε * ((m + 1 : ℕ) : ℝ) := by
      rw [div_lt_iff₀ (by positivity)] at hm
      push_cast
      exact hm
    have h4 : 1 < ε * (4 * (N : ℝ) * ((m + 1 : ℕ) : ℝ)) := by nlinarith
    rw [Real.dist_eq, abs_lt]
    constructor
    · have : ((⌊(4 * (N : ℝ) * ((m + 1 : ℕ) : ℝ)) * u τ i⌋ : ℤ) : ℝ) / (4 * (N : ℝ) * ((m + 1 : ℕ) : ℝ)) ≤ u τ i := by
        rw [div_le_iff₀ hM]; linarith
      linarith
    · have : u τ i - ε < ((⌊(4 * (N : ℝ) * ((m + 1 : ℕ) : ℝ)) * u τ i⌋ : ℤ) : ℝ) / (4 * (N : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
        rw [lt_div_iff₀ hM]; nlinarith
      linarith

end GlobalTheory.Mean4
