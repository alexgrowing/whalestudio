import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.Af.BA ComplexOrder in
theorem UpperTheory.adelicBaseChange_realPart :
    UpperTheory.V.Af.BA.RePart := by
  intro L _ _ N σ hσ k
  let A : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ :=
    fun w => Matrix.of fun i j => (((mat k w) i j).re : ℂ)
  have hre : ∀ w i j, ((mat k w) j i).re = ((mat k w) i j).re := by
    intro w i j
    have := (mat_herm k w).apply i j
    rw [← this]
    simp
  have hA : ∀ w, (A w).IsHermitian := by
    intro w
    ext i j
    simp [A, Matrix.conjTranspose_apply, hre w i j]
  have hmat : ∀ w, mat (mkHS A hA) w = A w := fun w => rfl
  have hAeq : ∀ w, A w = (1 / 2 : ℝ) • (mat k w + (mat k w).transpose) := by
    intro w
    ext i j
    have h1 := (mat_herm k w).apply i j
    have h2 : (mat k w) j i = star ((mat k w) i j) := by rw [← h1, star_star]
    simp only [A, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, h2]
    apply Complex.ext <;> simp <;> ring
  refine ⟨⟨mkHS A hA, ?_⟩, ?_, ?_⟩
  · intro w i j
    show ((mat (mkHS A hA) w) i j).im = 0
    rw [hmat]
    simp [A]
  · intro y
    show q (mkHS A hA) y = _
    have hz : ∀ w i, toR (sLat σ y) w i = star (toR y w i) := fun w i => hσ w (y i)
    simp only [q, qR]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hmat]
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum,
      ← Finset.sum_add_distrib, Finset.sum_div, hz]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [A, Matrix.of_apply, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · intro hk
    have hpsd : ∀ w, (A w).PosSemidef := by
      intro w
      rw [hAeq w]
      exact ((hk w).add (hk w).transpose).smul (by norm_num)
    refine ⟨fun w => by rw [hmat]; exact hpsd w, fun h0 => ?_⟩
    apply HS_ext
    intro w
    have hA0 : A w = 0 := by
      have := congrArg (fun x : HR L N => mat (x : HS L N) w) h0
      simpa [hmat, mat_zero] using this
    rw [mat_zero]
    apply ((hk w).trace_eq_zero_iff).mp
    have hd : ∀ i, (mat k w) i i = (((mat k w) i i).re : ℂ) := by
      intro i
      apply Complex.ext
      · simp
      · have := (mat_herm k w).apply i i
        have h3 := congrArg Complex.im this
        simp at h3
        simp
        linarith
    rw [Matrix.trace]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.diag_apply, hd i]
    have := congrFun (congrFun hA0 i) i
    simpa [A] using this
