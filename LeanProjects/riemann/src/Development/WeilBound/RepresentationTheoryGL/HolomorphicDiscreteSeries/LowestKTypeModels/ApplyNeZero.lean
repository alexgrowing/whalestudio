import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.OfIntegralHolds

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.LowestKTypeUnitIntegral

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.MainNotions.BridgeCSchur

variable {n : ℕ}

theorem apply_ne_zero {ε' : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    {ρ : UJ ε' → (H →L[ℂ] H)} (hirr : IsIrredOn (UJset ε') σ) {j : H' →L[ℂ] H} (hj0 : j ≠ 0)
    (hj : ∀ h : UJ ε', ∀ x, j (σ (um h) x) = ρ h (j x)) {w : H'} (hw : w ≠ 0) : j w ≠ 0 := by
  intro h0
  rcases irr_of hirr (LinearMap.ker (j : H' →ₗ[ℂ] H)) j.isClosed_ker (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      show j (σ (um g) v) = 0
      rw [hj, show j v = 0 from hv, map_zero]) with h | h
  · exact hw ((Submodule.mem_bot ℂ).1 (h ▸ (LinearMap.mem_ker.2 h0 : w ∈ LinearMap.ker (j : H' →ₗ[ℂ] H))))
  · exact hj0 (ContinuousLinearMap.ext fun x => by
      have : x ∈ LinearMap.ker (j : H' →ₗ[ℂ] H) := h ▸ Submodule.mem_top
      simpa using this)

theorem isom_of {ε' : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    {ρ : UJ ε' → (H →L[ℂ] H)} (hU : IsURepOn (UJset ε') σ) (hirr : IsIrredOn (UJset ε') σ) (hρ : URep ρ)
    (j : H' →L[ℂ] H) (hj : ∀ h : UJ ε', ∀ x, j (σ (um h) x) = ρ h (j x)) :
    ∃ c : ℂ, ∀ x, ⟪j x, j x⟫_ℂ = c * ⟪x, x⟫_ℂ := by
  obtain ⟨c, hc⟩ := schur_bounded (Set.range fun k : UJ ε' => σ (um k)) (by
      rintro _ ⟨k, rfl⟩
      refine ⟨k⁻¹, ?_⟩
      rw [ContinuousLinearMap.star_eq_adjoint]
      refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact (u_adj hU k x y).symm)
    (fun S hS hst => irr_of hirr S hS fun k => hst _ ⟨k, rfl⟩) (ContinuousLinearMap.adjoint j ∘L j) (by
      rintro _ ⟨k, rfl⟩
      refine ContinuousLinearMap.ext fun x => ext_inner_left ℂ fun y => ?_
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
      rw [hj]
      have e1 : ⟪j y, ρ k (j x)⟫_ℂ = ⟪ρ k⁻¹ (j y), j x⟫_ℂ := by rw [hρ.adj, inv_inv]
      rw [e1, ← hj, ← ContinuousLinearMap.adjoint_inner_right, u_adj hU, inv_inv])
  refine ⟨c, fun x => ?_⟩
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply, hc, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, inner_smul_right]

end PositivityTheory.RgHe.LowestKTypeUnitIntegral
