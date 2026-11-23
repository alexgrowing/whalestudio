import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian

open MeasureTheory

namespace GlobalTheory

private theorem measurePreserving_piCurry_symm_fin_two (ι : Type) [Fintype ι] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (_ : ι) (_ : Fin 2) => ℝ)).symm
      volume volume := by
  classical
  refine ⟨(MeasurableEquiv.piCurry _).symm.measurable, ?_⟩
  symm
  rw [volume_pi]
  refine Measure.pi_eq fun s hs => ?_
  rw [(MeasurableEquiv.piCurry _).symm.map_apply]
  have hpre : (MeasurableEquiv.piCurry (fun (_ : ι) (_ : Fin 2) => ℝ)).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => Set.univ.pi fun k => s ⟨i, k⟩ := by
    ext x
    simp [Set.mem_pi, Sigma.forall, MeasurableEquiv.coe_piCurry_symm, Sigma.uncurry]
  rw [hpre, volume_pi_pi]
  simp only [volume_pi_pi]
  rw [← Finset.univ_sigma_univ, Finset.prod_sigma]

theorem measurePreserving_of_norm_sq_eq_sum_complex_coords
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (ι : Type) [Fintype ι] (e : V ≃L[ℝ] (ι → ℂ))
    (he : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) : MeasurePreserving e volume volume := by
  classical
  let Φ : (ι → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Σ _ : ι, Fin 2) :=
    (LinearEquiv.piCongrRight fun _ => Complex.basisOneI.equivFun).trans
      ((LinearEquiv.piCurry ℝ fun (_ : ι) (_ : Fin 2) => ℝ).symm.trans
        (WithLp.linearEquiv 2 ℝ _).symm)
  have hΦ : ∀ z, ‖Φ z‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : ∀ k, Φ z ⟨i, k⟩ = Complex.basisOneI.repr (z i) k := fun k => rfl
    simp only [hc, Fin.sum_univ_two, Complex.coe_basisOneI_repr, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  let F : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Σ _ : ι, Fin 2) :=
    { toLinearEquiv := e.toLinearEquiv.trans Φ
      norm_map' := fun v => by
        have h : ‖Φ (e v)‖ ^ 2 = ‖v‖ ^ 2 := by rw [hΦ, he]
        exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h }
  let G : (ι → ℂ) ≃ᵐ EuclideanSpace ℝ (Σ _ : ι, Fin 2) :=
    (MeasurableEquiv.piCongrRight fun _ => Complex.measurableEquivPi).trans
      ((MeasurableEquiv.piCurry fun (_ : ι) (_ : Fin 2) => ℝ).symm.trans
        (MeasurableEquiv.toLp 2 _))
  have hG : MeasurePreserving G volume volume :=
    (PiLp.volume_preserving_toLp _).comp ((measurePreserving_piCurry_symm_fin_two ι).comp
      (volume_preserving_pi fun _ => Complex.volume_preserving_equiv_pi))
  have hFG : (F : V → EuclideanSpace ℝ (Σ _ : ι, Fin 2)) = G ∘ e := by
    funext v
    rfl
  have hF : MeasurePreserving (G ∘ e) volume volume := hFG ▸ F.measurePreserving
  exact hG.comp_left_iff.1 hF

end GlobalTheory
