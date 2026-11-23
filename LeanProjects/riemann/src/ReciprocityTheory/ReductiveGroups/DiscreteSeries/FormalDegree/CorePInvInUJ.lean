import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacAll

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem inv_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    inUJ ε (Jm ε * gᴴ * Jm ε) ∧ (Jm ε * gᴴ * Jm ε) * g = 1 ∧ g * (Jm ε * gᴴ * Jm ε) = 1 := by
  have hJ : Jm ε * Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJt : (Jm ε)ᴴ = Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hg' : gᴴ * (Jm ε * g) = Jm ε := by
    unfold inUJ at hg
    rw [← Matrix.mul_assoc]; exact hg
  have h1 : Jm ε * gᴴ * Jm ε * g = 1 := by
    simp only [Matrix.mul_assoc]; rw [hg', hJ]
  have h2 : g * (Jm ε * gᴴ * Jm ε) = 1 := by
    first
    | exact mul_eq_one_comm.mp h1
    | exact Matrix.mul_eq_one_comm.mp h1
    | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp h1
  have h3 : ∀ X : Matrix (Fin n) (Fin n) ℂ, g * (Jm ε * (gᴴ * X)) = Jm ε * X := fun X => by
    calc g * (Jm ε * (gᴴ * X)) = g * (Jm ε * gᴴ * Jm ε) * (Jm ε * X) := by
          simp only [Matrix.mul_assoc, hJJ]
      _ = Jm ε * X := by rw [h2, Matrix.one_mul]
  refine ⟨?_, h1, h2⟩
  unfold inUJ
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJt, Matrix.mul_assoc, hJJ, h3]

theorem coreP {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Measure.map (actR (ε := ε) g) (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) =
      volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z) := by
  obtain ⟨hh, hhg, hgh⟩ := inv_inUJ hg
  set h := Jm ε * gᴴ * Jm ε with hdef
  have hleft : ∀ z, actR (ε := ε) h (actR g z) = z := fun z => by
    rw [← actR_mul hg hh, hgh, actR_one]
  have hright : ∀ z, actR (ε := ε) g (actR h z) = z := fun z => by
    rw [← actR_mul hh hg, hhg, actR_one]
  have hmeas : Measurable (actR (ε := ε) g) := (JacB.actR_continuous hg).measurable
  ext A hA
  rw [Measure.map_apply hmeas hA, withDensity_apply _ hA, withDensity_apply _ (hmeas hA)]
  have himg : actR (ε := ε) g '' (actR g ⁻¹' A) = A :=
    Set.image_preimage_eq A (fun y => ⟨actR h y, hright y⟩)
  calc ∫⁻ z in actR g ⁻¹' A, ENNReal.ofReal (Jac z)
        = ∫⁻ z in actR g ⁻¹' A, ENNReal.ofReal |(fderiv ℝ (actR (ε := ε) g) z).det| *
            ENNReal.ofReal (Jac (actR g z)) := by
          refine lintegral_congr (fun z => ?_)
          rw [← ENNReal.ofReal_mul (abs_nonneg _)]
          rw [← jacAll hg z]
    _ = ∫⁻ z in actR g '' (actR g ⁻¹' A), ENNReal.ofReal (Jac z) :=
          (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hmeas hA)
            (fun z _ => (jall_diff hg z).hasFDerivAt.hasFDerivWithinAt)
            (fun x _ y _ hxy => by rw [← hleft x, hxy, hleft y]) (fun z => ENNReal.ofReal (Jac z))).symm
    _ = ∫⁻ z in A, ENNReal.ofReal (Jac z) := by rw [himg]

end ReciprocityTheory.ChartRestriction.DS
