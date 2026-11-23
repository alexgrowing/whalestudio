import Mathlib
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.CompanionTheory.HilbMoll

variable {n : ℕ}

theorem opConv_mem_of_isClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (W : Submodule ℂ H) (hWc : IsClosed (W : Set H)) (hWs : ∀ g ∈ UJset ε, ∀ x ∈ W, σ g x ∈ W)
    {x : H} (hx : x ∈ W) : opConv ε σ α x ∈ W := by
  have : CompleteSpace W := hWc.completeSpace_coe
  unfold opConv
  by_cases hint : Integrable (fun g : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) x)
      (Formalism.REAL.muG ε)
  · have hfix : ∀ g : Formalism.REAL.UJ ε, W.starProjection (α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) x) =
        α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) x := fun g =>
      Submodule.starProjection_eq_self_iff.2 (W.smul_mem _ (hWs _ (arb_umat_mem g) x hx))
    have h := W.starProjection.integral_comp_comm hint
    simp only [hfix] at h
    rw [h]
    exact W.starProjection_apply_mem _
  · rw [integral_undef hint]
    exact W.zero_mem

theorem stepMoll : PositivityTheory.RgDs.Hilb.StepMoll := by
  intro n ε W S hWc hWs hSf hSW _
  have := hSf
  obtain ⟨α, hadd, hsmul, hαK, hαsm, hαS⟩ := exists_moll_data (rreg_isURepOn ε) S
  let A : L2 ε →ₗ[ℂ] L2 ε := { toFun := opConv ε (rreg ε) α, map_add' := hadd, map_smul' := hsmul }
  have hAv : ∀ v, A v = opConv ε (rreg ε) α v := fun v => rfl
  refine ⟨A, fun k hk x => (hαK k hk x).symm, ?_, ?_, ?_⟩
  · intro w hw h0
    have h1 := hαS w hw
    rw [← hAv, h0, zero_sub, norm_neg] at h1
    have h2 : ‖w‖ ≤ 0 := by linarith
    exact norm_le_zero_iff.1 h2
  · rintro _ ⟨w, _, rfl⟩
    exact (mem_smD_iff ε (rreg ε) _).2 (hαsm w)
  · rintro _ ⟨w, hw, rfl⟩
    exact opConv_mem_of_isClosed ε (rreg ε) α W hWc hWs (hSW hw)

end GlobalTheory.CompanionTheory.HilbMoll
