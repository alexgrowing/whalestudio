import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Polynomial

private theorem winDiff (ℓ : ℕ) [Fact ℓ.Prime] (j₀ lo : ℤ) (L D : ℕ) (T : Finset ℤ)
    (hT : ∀ j ∈ T, lo ≤ j₀ - j ∧ j₀ - j < lo + L) (h0 : j₀ ∉ T)
    (hD : ∀ j ∈ T, |j₀ - j| ≤ (D : ℤ)) :
    ((∑ j ∈ T, padicValInt ℓ (j₀ - j) : ℕ) : ℝ) ≤
      (L : ℝ) / ((ℓ : ℝ) - 1) + Real.logb (ℓ : ℝ) (D : ℝ) := by
  have hinj : Set.InjOn (fun j : ℤ => j₀ - j) (T : Set ℤ) := by
    intro x _ y _ h
    simp only at h
    omega
  have hre : ∑ j ∈ T, padicValInt ℓ (j₀ - j) =
      ∑ i ∈ T.image (fun j : ℤ => j₀ - j), padicValInt ℓ i :=
    (Finset.sum_image hinj).symm
  rw [hre]
  apply Formalism.WindowSums.arc_WindowSum ℓ lo L D
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    have := hT j hj
    rw [Finset.mem_Ico]
    omega
  · intro hi
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.1 hi
    have : j = j₀ := by omega
    exact h0 (this ▸ hj)
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    exact hD j hj

theorem g_ideal_valuation_statement : LemmaGIdeal := by
  intro ℓ _ R _ _ c hc h η S b a S₂ hb hbS hS₂
  have hℓ2 : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (Fact.out : ℓ.Prime).two_le
  set S₁ := Finset.Icc ((b : ℤ) - a + 1) (b : ℤ) with hS₁def
  have m2 : ∀ r ∈ S₂, ((b : ℤ) + 1 ≤ r ∧ r ≤ b + S + a) ∨ (1 - (η : ℤ) ≤ r ∧ r ≤ η + a) := by
    intro r hr
    simpa only [Finset.mem_union, Finset.mem_Icc] using hS₂ hr
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    rw [hS₁def, Finset.mem_Icc] at hr1
    have := m2 r hr2
    omega
  have hlag := Formalism.LIFT.lift_LagrangeIdealInt ℓ R S₁ S₂ c hdisj
    (fun x _ y _ hxy => hc x y hxy)
  refine ⟨S₁.sup fun j₀ => (∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) +
      ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j), ?_, hlag⟩

  have hH1 : (1 : ℝ) ≤ ((h + η : ℕ) : ℝ) := by
    have : 1 ≤ h + η := by omega
    exact_mod_cast this
  have hlog : Real.logb (ℓ : ℝ) ((h + η : ℕ) : ℝ) ≤ lam ℓ (h + η) := by
    unfold lam
    have := Real.logb_le_logb_of_le (b := (ℓ : ℝ)) (by linarith) (by linarith)
      (show ((h + η : ℕ) : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) by linarith)
    linarith
  have hlam0 : 0 ≤ lam ℓ (h + η) := by
    unfold lam
    have := Real.logb_nonneg (b := (ℓ : ℝ)) (by linarith)
      (show (1 : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) by linarith)
    linarith
  have hden : 0 < (ℓ : ℝ) - 1 := by linarith
  have key : ∀ j₀ ∈ S₁, ((((∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) +
      ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j) : ℕ)) : ℝ) ≤
      (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) + 3 * lam ℓ (h + η) := by
    intro j₀ hj₀
    rw [hS₁def, Finset.mem_Icc] at hj₀
    rw [← Finset.sum_filter_add_sum_filter_not S₂ (fun j => (b : ℤ) + 1 ≤ j)]
    push_cast
    have w1 := winDiff ℓ j₀ (j₀ - b) a (h + η) (S₁.erase j₀)
      (by
        intro j hj
        rw [Finset.mem_erase, hS₁def, Finset.mem_Icc] at hj
        omega)
      (by simp)
      (by
        intro j hj
        rw [Finset.mem_erase, hS₁def, Finset.mem_Icc] at hj
        rw [abs_le]
        push_cast
        constructor <;> omega)
    have w2 := winDiff ℓ j₀ (j₀ - b - S - a) (S + a) (h + η)
      (S₂.filter (fun j => (b : ℤ) + 1 ≤ j))
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        push_cast
        omega)
      (by
        rw [Finset.mem_filter]
        omega)
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        rw [abs_le]
        push_cast
        constructor <;> omega)
    have w3 := winDiff ℓ j₀ (j₀ - η - a) (2 * η + a) (h + η)
      (S₂.filter (fun j => ¬ (b : ℤ) + 1 ≤ j))
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        push_cast
        omega)
      (by
        rw [Finset.mem_filter]
        intro hh
        have := m2 j₀ hh.1
        omega)
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        rw [abs_le]
        push_cast
        constructor <;> omega)
    push_cast at w1 w2 w3
    have hsum : (a : ℝ) / ((ℓ : ℝ) - 1) + ((S : ℝ) + (a : ℝ)) / ((ℓ : ℝ) - 1) +
        (2 * (η : ℝ) + (a : ℝ)) / ((ℓ : ℝ) - 1) =
        (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) := by ring
    push_cast at hlog
    linarith
  rcases S₁.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sup_empty]
    simp only [Nat.bot_eq_zero, Nat.cast_zero]
    have : 0 ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) := by positivity
    linarith
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup S₁ hne
      (fun j₀ => (∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) + ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j))
    rw [hjeq]
    exact key j hj

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
