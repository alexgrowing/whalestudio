import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomKillHighOrder
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_ext_of_isNilpotent :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ ψ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        (∀ i, φ (X i) = ψ (X i)) → φ = ψ := by
  intro k _ σ _ A _ _ φ ψ hφ h
  classical
  obtain ⟨N₁, h₁⟩ := GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ A φ hφ
  obtain ⟨N₂, h₂⟩ := GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ A ψ (fun i => h i ▸ hφ i)
  have hp : φ.comp (MvPolynomial.coeToMvPowerSeries.algHom k) =
      ψ.comp (MvPolynomial.coeToMvPowerSeries.algHom k) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [h i]
  have hm : ∀ (α : σ →₀ ℕ) (c : k), φ (monomial α c) = ψ (monomial α c) := by
    intro α c
    have := DFunLike.congr_fun hp (MvPolynomial.monomial α c)
    simpa [MvPolynomial.coe_monomial] using this
  have hfin : {α : σ →₀ ℕ | α.degree ≤ N₁ + N₂}.Finite := Finsupp.finite_of_degree_le _
  apply AlgHom.ext
  intro f
  set p : MvPowerSeries σ k := ∑ α ∈ hfin.toFinset, monomial α (coeff α f) with hpdef
  have hc : ∀ α : σ →₀ ℕ, α.degree ≤ N₁ + N₂ → coeff α (f - p) = 0 := by
    intro α hα
    rw [map_sub, hpdef, map_sum, Finset.sum_eq_single α]
    · simp
    · intro β _ hβ
      rw [coeff_monomial_ne hβ.symm]
    · intro hn
      exact absurd (by simpa using hα) hn
  have e₁ : φ (f - p) = 0 := h₁ _ (fun α hα => hc α (by omega))
  have e₂ : ψ (f - p) = 0 := h₂ _ (fun α hα => hc α (by omega))
  have e₃ : φ p = ψ p := by
    rw [hpdef, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun α _ => hm _ _)
  rw [map_sub, sub_eq_zero] at e₁ e₂
  rw [e₁, e₂, e₃]

end GlobalTheory
