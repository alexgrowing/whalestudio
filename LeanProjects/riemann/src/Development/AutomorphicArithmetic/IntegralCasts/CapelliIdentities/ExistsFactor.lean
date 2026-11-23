import Mathlib

theorem UpperTheory.Reformulated.B.ExistsFactor.exists_factor :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (e : Matrix (Fin n) (Fin n) K),
    e * e = e →
      ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) K) (N : Matrix (Fin r) (Fin n) K),
        N * M = (1 : Matrix (Fin r) (Fin r) K) ∧ M * N = e := by
  intro K _ n e he
  let f : (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.toLin' e
  have hf : ∀ v, f (f v) = f v := by
    intro v
    have h : f.comp f = f := by
      show (Matrix.toLin' e).comp (Matrix.toLin' e) = Matrix.toLin' e
      rw [← Matrix.toLin'_mul, he]
    exact LinearMap.congr_fun h v
  let b := Module.finBasis K (LinearMap.range f)
  let c := Pi.basisFun K (Fin n)
  refine ⟨Module.finrank K (LinearMap.range f),
    LinearMap.toMatrix b c (LinearMap.range f).subtype,
    LinearMap.toMatrix c b f.rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp]
    have h : f.rangeRestrict.comp (LinearMap.range f).subtype = LinearMap.id := by
      apply LinearMap.ext
      rintro ⟨x, v, rfl⟩
      apply Subtype.ext
      exact hf v
    rw [h, LinearMap.toMatrix_id]
  · rw [← LinearMap.toMatrix_comp]
    have h : (LinearMap.range f).subtype.comp f.rangeRestrict = f := by
      apply LinearMap.ext
      intro v
      rfl
    rw [h]
    show LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)) (Matrix.toLin' e) = e
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
