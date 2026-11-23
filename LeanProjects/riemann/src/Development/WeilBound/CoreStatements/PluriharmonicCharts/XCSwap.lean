import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_swap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → ∃ (k₀ : K) (ca cb : Fin N), M.blk (τ, a) = some k₀ ∧ (ca : ℕ) = lastCol N j a ∧ (cb : ℕ) = ca + 1 ∧ ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) ∧ (∑ p, xiCoef τ a p * M.dy p k₀) = -2 ∧ ∀ p, p ≠ (τ, a) → M.dy p k₀ = 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b hab hcase
  have hjN := M.j_le
  have hbN := b.isLt
  have ha1 : (a : ℕ) + 1 ≠ j := by omega
  have ha2 : (a : ℕ) + 1 ≠ N := by omega
  have hprop : IsProperStep N j a := ⟨ha1, ha2⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, M.blk (τ, a) = some k₀ := by
    cases h : M.blk (τ, a) with
    | none => exact ((M.blk_none (τ, a)).1 h hprop).elim
    | some k => exact ⟨k, rfl⟩
  have hdy : ∀ p, M.dy p k₀ = if p = (τ, a) then 1 else 0 := by
    intro p
    unfold FlagModel.dy
    have hnot : ¬ ∀ p' : Ψ × Fin N, M.blk p' ≠ some k₀ := fun h => h (τ, a) hk₀
    rw [dif_neg hnot]
    by_cases hp : p = (τ, a)
    · subst hp
      simp [hk₀]
    · rw [if_neg hp, if_neg]
      intro h
      exact hp (M.blk_inj p (τ, a) k₀ h hk₀)
  have hlast : lastCol N j a < N ∧ lastCol N j a + 1 < N ∧
      (lastCol N j a < N - j ↔ lastCol N j a + 1 < N - j) := by
    unfold lastCol
    split_ifs with h <;> omega
  refine ⟨k₀, ⟨lastCol N j a, hlast.1⟩, ⟨lastCol N j a + 1, hlast.2.1⟩, hk₀, rfl, rfl, hlast.2.2, ?_, ?_⟩
  · simp only [hdy, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [xiCoef]
  · intro p hp
    rw [hdy p, if_neg hp]
