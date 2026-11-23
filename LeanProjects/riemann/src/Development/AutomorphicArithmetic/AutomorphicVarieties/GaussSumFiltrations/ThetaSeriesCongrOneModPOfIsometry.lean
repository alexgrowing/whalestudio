import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.QExpansionLinearCombination
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntMatrixIsometryPrimeOrderLatticeStability
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.NormSumFreeOrbitsLeInvPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.LatticePeriodicFunctionRangeFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramQuadFormTotallyPositiveProperness
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesHolomorphicQExpansionOfBoundedCoeff

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem th_congr_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → Small ι (p : ℝ)⁻¹ (th G Φ - 1) := by
  intro F _ _ _ p _ ι κ _ _ G S t hL Φ hΦ
  obtain ⟨⟨N, hN, hNp, hSB⟩, hinv, hbd, h0⟩ := hΦ
  have hp : p.Prime := Fact.out
  obtain ⟨hQ, hact, -, -⟩ := _root_.GlobalTheory.T.intMatrix_isometry_prime_order_lattice_stability F p hp κ G S t hL
  obtain ⟨hTP, -, hfin⟩ := _root_.GlobalTheory.T.evenPosGram_quadForm_totallyPositive_properness F κ G hL.pos
  obtain ⟨B, hB⟩ := ((_root_.GlobalTheory.T.lattice_periodic_function_range_finite F κ N Φ hN hSB).image (fun w => ‖w‖)).bddAbove
  have hB' : ∀ x, ‖Φ x‖ ≤ B := fun x => hB ⟨Φ x, ⟨x, rfl⟩, rfl⟩
  obtain ⟨-, -, -, hq⟩ := _root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F κ G hL.pos ((N:F)⁻¹) Φ B hSB.1 hB'
  have hc := (_root_.GlobalTheory.T.qExpansion_linear_combination F _ _ _ _ (1:ℂ) hq hq).2.2.2
  have hq1 := (_root_.GlobalTheory.T.qExpansion_linear_combination F _ _ _ _ (1:ℂ) hq hc).2.2.1
  refine ⟨_, hq1, fun ξ => ?_⟩
  simp only [Pi.sub_apply]
  have hfs := hfin ((N:F)⁻¹) ξ
  rw [finsum_mem_eq_finite_toFinset_sum _ hfs]
  by_cases hξ : ξ = 0
  · subst hξ
    have hz : hfs.toFinset = {0} := by
      ext x
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hx⟩
        by_contra hne
        have h1 := hTP x hne
        rw [hx] at h1
        obtain ⟨v⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace F))
        have h2 := h1 v
        simp [reAt] at h2
      · rintro rfl
        exact ⟨zero_mem _, by simp [QF, BF]⟩
    rw [hz, Finset.sum_singleton, if_pos rfl, map_sub, map_one]
    exact h0
  · rw [if_neg hξ, sub_zero]
    apply _root_.GlobalTheory.T.norm_sum_free_orbits_le_inv_prime p ι (κ → F) (fun x => S.map Int.cast *ᵥ x) hfs.toFinset Φ
    · intro x hx
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
      exact ⟨((hact x).2.2.2 _).2 hx.1, ((hQ x x).2).trans hx.2⟩
    · intro x _
      exact (hact x).1
    · intro x hx h
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
      apply hξ
      rw [← hx.2, (hact x).2.1 h]
      simp [QF, BF]
    · intro x _
      exact hinv x
    · intro x _
      exact hbd x

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_congr_one_mod_p_of_isometry : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → Small ι (p : ℝ)⁻¹ (th G Φ - 1) := by
  first | exact @GlobalTheory.HilbertThetaSeries.th_congr_one | exact GlobalTheory.HilbertThetaSeries.th_congr_one | (intros; apply GlobalTheory.HilbertThetaSeries.th_congr_one <;> assumption)
