import Mathlib

private theorem exists_ker {n g : ℕ} (f : (Fin n → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (U : Submodule ℂ (Fin g → ℂ)) (hU : ∀ y, f y ∈ U)
    (hI : ∀ y, f y = 0 → f (Complex.I • y) = 0) :
    ∃ K : Submodule ℂ (Fin n → ℂ), (∀ y, y ∈ K ↔ f y = 0) ∧
      n ≤ Module.finrank ℂ K + Module.finrank ℂ U := by
  let K : Submodule ℂ (Fin n → ℂ) :=
    { carrier := {y | f y = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun z y hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        have hz : z • y = z.re • y + z.im • (Complex.I • y) := by
          ext i
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im z]
          ring
        rw [hz, map_add, map_smul, map_smul, hy, hI y hy, smul_zero, smul_zero, add_zero] }
  refine ⟨K, fun y => Iff.rfl, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : LinearMap.ker f = K.restrictScalars ℝ := by
    ext y
    rfl
  have h3 : LinearMap.range f ≤ U.restrictScalars ℝ := by
    rintro _ ⟨y, rfl⟩
    exact hU y
  have h4 := Submodule.finrank_mono h3
  have h5 : Module.finrank ℝ (U.restrictScalars ℝ) = 2 * Module.finrank ℂ U :=
    finrank_real_of_complex U
  have h6 : Module.finrank ℝ (K.restrictScalars ℝ) = 2 * Module.finrank ℂ K :=
    finrank_real_of_complex K
  have h7 : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [finrank_real_of_complex]; simp
  rw [h2, h6, h7] at h1
  omega

theorem UpperTheory.hermitian_positive_symplectic :
    ∀ {g j j' : ℕ} (p : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (H : Matrix (Fin g) (Fin g) ℂ)
        (S : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (c : ℝ) (U U' : Submodule ℂ (Fin g → ℂ)),
        (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (dotProduct z (H.mulVec (star z))).re) →
        IsUnit S.det → 0 < c →
        (∀ y y', (dotProduct (p y) (H.mulVec (star (p y')))).im =
          2 * (Complex.I * (c : ℂ) * dotProduct (star y') (S.mulVec y)).re) →
        Module.finrank ℂ U = j' → Module.finrank ℂ U' = j →
        (∀ y, p y - Complex.I • p (Complex.I • y) ∈ U) →
        (∀ y, p y + Complex.I • p (Complex.I • y) ∈ U') →
        ∃ K K' : Submodule ℂ (Fin (j + j') → ℂ),
          j ≤ Module.finrank ℂ K ∧ j' ≤ Module.finrank ℂ K' ∧
          (∀ y ∈ K, p y - Complex.I • p (Complex.I • y) = 0) ∧
          (∀ y ∈ K', p y + Complex.I • p (Complex.I • y) = 0) ∧
          (∀ y ∈ K, y ≠ 0 → 0 < (dotProduct (star y) (S.mulVec y)).re) ∧
          (∀ y ∈ K', y ≠ 0 → (dotProduct (star y) (S.mulVec y)).re < 0) ∧
          ∀ y ∈ K, ∀ y' ∈ K', dotProduct (star y') (S.mulVec y) = 0 := by
  intro g j j' p H S c U U' hH hS hc hp hU hU' hA hB
  let Q : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun y => Complex.I • p (Complex.I • y)
      map_add' := fun a b => by rw [smul_add, map_add, smul_add]
      map_smul' := fun r a => by
        rw [smul_comm Complex.I r a, map_smul, smul_comm Complex.I r]; rfl }
  have hII : ∀ {m : ℕ} (v : Fin m → ℂ), Complex.I • Complex.I • v = -v := by
    intro m v
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  have eA : ∀ y, p y - Complex.I • p (Complex.I • y) = 0 →
      p (Complex.I • y) = -(Complex.I • p y) := by
    intro y hy
    rw [sub_eq_zero.mp hy, hII, neg_neg]
  have eB : ∀ y, p y + Complex.I • p (Complex.I • y) = 0 →
      p (Complex.I • y) = Complex.I • p y := by
    intro y hy
    rw [eq_neg_of_add_eq_zero_left hy, smul_neg, hII, neg_neg]
  obtain ⟨K, hK, dK⟩ := exists_ker (p - Q) U hA (by
    intro y hy
    change p (Complex.I • y) - Complex.I • p (Complex.I • Complex.I • y) = 0
    rw [hII, map_neg, eA y hy, smul_neg, sub_self])
  obtain ⟨K', hK', dK'⟩ := exists_ker (p + Q) U' hB (by
    intro y hy
    change p (Complex.I • y) + Complex.I • p (Complex.I • Complex.I • y) = 0
    rw [hII, map_neg, eB y hy, smul_neg, add_neg_cancel])
  have hp' : ∀ y y', (dotProduct (p y) (H.mulVec (star (p y')))).im =
      -(2 * c * (dotProduct (star y') (S.mulVec y)).im) := by
    intro y y'
    rw [hp]
    simp
    ring
  have hinj : ∀ y, y ≠ 0 → p y ≠ 0 := by
    intro y hy h0
    apply hy
    have hz : ∀ y', (dotProduct (star y') (S.mulVec y)).im = 0 := by
      intro y'
      have h := hp' y y'
      rw [h0, zero_dotProduct, Complex.zero_im] at h
      have : c * (dotProduct (star y') (S.mulVec y)).im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hc.ne'
    have hSy : S.mulVec y = 0 := by
      ext i
      have h1 := hz (Pi.single i 1)
      have h2 := hz (Pi.single i Complex.I)
      simp [← Pi.single_star] at h1 h2
      apply Complex.ext <;> simp [h1, h2]
    exact Matrix.eq_zero_of_mulVec_eq_zero hS.ne_zero hSy
  refine ⟨K, K', by omega, by omega, fun y hy => (hK y).mp hy, fun y hy => (hK' y).mp hy,
    ?_, ?_, ?_⟩
  · intro y hy h0
    have h1 := hH _ (hinj y h0)
    have h2 := hp' (Complex.I • y) y
    rw [eA y ((hK y).mp hy)] at h2
    simp [Matrix.mulVec_smul] at h2
    by_contra hn
    have := mul_nonneg hc.le (neg_nonneg.mpr (not_lt.mp hn))
    linarith
  · intro y hy h0
    have h1 := hH _ (hinj y h0)
    have h2 := hp' (Complex.I • y) y
    rw [eB y ((hK' y).mp hy)] at h2
    simp [Matrix.mulVec_smul] at h2
    by_contra hn
    have := mul_nonneg hc.le (not_lt.mp hn)
    linarith
  · intro y hy y' hy'
    have e1 := eA y ((hK y).mp hy)
    have e2 := eB y' ((hK' y').mp hy')
    have h1 := hp' y y'
    have h2 := hp' (Complex.I • y) y'
    have h3 := hp' y (Complex.I • y')
    have h4 := hp' (Complex.I • y) (Complex.I • y')
    rw [e1] at h2 h4
    rw [e2] at h3 h4
    simp [Matrix.mulVec_smul, Matrix.mulVec_neg] at h2 h3 h4
    have r1 : c * (dotProduct (star y') (S.mulVec y)).re = 0 := by linarith
    have r2 : c * (dotProduct (star y') (S.mulVec y)).im = 0 := by linarith
    exact Complex.ext ((mul_eq_zero.mp r1).resolve_left hc.ne')
      ((mul_eq_zero.mp r2).resolve_left hc.ne')
