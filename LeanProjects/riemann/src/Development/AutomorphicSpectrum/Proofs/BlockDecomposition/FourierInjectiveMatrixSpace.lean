import Mathlib

open MeasureTheory
open scoped Matrix FourierTransform InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.FourierMat

noncomputable def entries (m n : ℕ) :
    (Fin m → Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin m × Fin n) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => WithLp.toLp 2 (fun p => u p.1 p.2)
      invFun := fun x a j => x (a, j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem entries_apply (m n : ℕ) (u : Fin m → Fin n → ℂ) (p : Fin m × Fin n) :
    entries m n u p = u p.1 p.2 := rfl

theorem pairing {m n : ℕ} {s : ℂ} (hs : s ≠ 0) (w : EuclideanSpace ℂ (Fin m × Fin n))
    (v : Fin m → Fin n → ℂ) :
    (s * Matrix.trace ((Matrix.of fun a j => -(w (a, j)) / conj s)ᴴ * Matrix.of v)).re =
      -(⟪entries m n v, w⟫_ℝ) := by
  have key : s * Matrix.trace ((Matrix.of fun a j => -(w (a, j)) / conj s)ᴴ * Matrix.of v)
      = -(∑ a, ∑ j, conj (w (a, j)) * v a j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply]
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_div₀, star_neg, Complex.star_def, Complex.conj_conj]
    field_simp
  rw [key, PiLp.inner_apply, Fintype.sum_prod_type, Complex.neg_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.inner]
  simp only [entries_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem fourier_uniqueness : ∀ (m n : ℕ) (s : ℂ), s ≠ 0 → ∀ g : (Fin m → Fin n → ℂ) → ℂ,
    Continuous g → Integrable g →
    (∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I *
      ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) → g = 0 := by
  intro m n s hs g hgc hgi hF
  have hemb : MeasurableEmbedding (entries m n) := (entries m n).toHomeomorph.measurableEmbedding
  have hC : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  have hV1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ => volume)
  have hV2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ => volume)
  have : (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ))).IsAddHaarMeasure :=
    (entries m n).isAddHaarMeasure_map volume
  have hμ := Measure.isAddLeftInvariant_eq_smul
    (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ)))
    (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n)))
  have hcpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ)))
    (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n)))
  have hcomp : (fun x => g ((entries m n).symm x)) ∘ (entries m n) = g := by
    funext v
    simp
  have hGmap : Integrable (fun x => g ((entries m n).symm x))
      (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ))) :=
    hemb.integrable_map_iff.mpr (by rw [hcomp]; exact hgi)
  rw [hμ, ← Measure.coe_nnreal_smul] at hGmap
  have hGi : Integrable (fun x => g ((entries m n).symm x))
      (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n))) :=
    (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hcpos.ne') ENNReal.coe_ne_top).mp hGmap
  have hGc : Continuous (fun x => g ((entries m n).symm x)) :=
    hgc.comp (entries m n).symm.continuous
  have hFG : FourierTransform.fourier (fun x => g ((entries m n).symm x)) = 0 := by
    funext w
    rw [Real.fourier_eq', Pi.zero_apply]
    have h0 := hF (fun a j => -(w (a, j)) / conj s)
    have h1 : ∫ x, Complex.exp (↑(-2 * Real.pi * ⟪x, w⟫_ℝ) * Complex.I) • g ((entries m n).symm x)
        ∂(Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ))) = 0 := by
      rw [hemb.integral_map]
      refine Eq.trans ?_ h0
      congr 1
      funext v
      rw [pairing hs w v]
      simp only [ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul]
      congr 2
      push_cast
      ring
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_zero] at h1
    exact h1.resolve_left (by exact_mod_cast hcpos.ne')
  have hinv := Continuous.fourierInv_fourier_eq hGc hGi
    (by rw [hFG]; exact integrable_zero _ _ _)
  rw [hFG] at hinv
  funext v
  have hx := congrFun hinv ((entries m n) v)
  rw [Real.fourierInv_eq'] at hx
  simp only [Pi.zero_apply, smul_zero, integral_zero, ContinuousLinearEquiv.symm_apply_apply] at hx
  rw [Pi.zero_apply]
  exact hx.symm

end GlobalTheory.CompanionTheory.FourierMat
