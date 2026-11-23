import Mathlib

private def UpperTheory.matrixSpaceLinearEquiv (n : ℕ) : (Fin n → Fin n → ℂ) ≃ₗ[ℂ] (Fin n → Fin n → ℂ) where
  toFun x := fun i j => x j i
  invFun x := fun i j => x j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def UpperTheory.matrixLeftMulLinearMap (n : ℕ) (a : Fin n → Fin n → ℂ) :
    (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  (UpperTheory.matrixSpaceLinearEquiv n).toLinearMap ∘ₗ
    (LinearMap.pi fun j : Fin n => (Matrix.toLin' (Matrix.of a)).comp (LinearMap.proj j)) ∘ₗ
    (UpperTheory.matrixSpaceLinearEquiv n).symm.toLinearMap

private theorem UpperTheory.det_leftMulLinearMap (n : ℕ) (a : Fin n → Fin n → ℂ) :
    LinearMap.det (UpperTheory.matrixLeftMulLinearMap n a) = (Matrix.of a).det ^ n := by
  unfold UpperTheory.matrixLeftMulLinearMap
  rw [LinearMap.det_conj, LinearMap.det_pi]
  simp

theorem UpperTheory.map_left_mul_volume_eq :
    ∀ (n : ℕ) (a : Fin n → Fin n → ℂ), ‖(Matrix.of a).det‖ = 1 →
        MeasureTheory.Measure.map (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Fin n → ℂ)) = MeasureTheory.volume := by
  intro n a ha
  have hf : (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x))
      = ⇑((UpperTheory.matrixLeftMulLinearMap n a).restrictScalars ℝ) := by
    funext x i j
    rfl
  have hd : LinearMap.det ((UpperTheory.matrixLeftMulLinearMap n a).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, UpperTheory.det_leftMulLinearMap, Algebra.norm_complex_apply, map_pow,
      Complex.normSq_eq_norm_sq, ha]
    simp
  haveI h1 : (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI h2 : (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Fin n → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  rw [hf, MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar _
    (by rw [hd]; exact one_ne_zero), hd]
  simp
