import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.prj_eigIn_of_eigenvector_prj :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (A : H →L[ℂ] H), IsClosed (W : Set H) → IsSelfAdjoint A → ∀ (v : H) (μ x : ℝ), A (prj W v) = (μ : ℂ) • prj W v → prj (eigIn W A x) v = if x = μ then prj W v else 0 := by
  intro H _ _ _ W A hW hA v μ x hv
  have hWc : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hPW : prj W v ∈ W := by
    have : prj W v ∈ W.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hWc] at this
  have hperp : ∀ w ∈ W, inner ℂ w (v - prj W v) = 0 := by
    intro w hw
    have : v - prj W v ∈ W.topologicalClosureᗮ := Submodule.sub_starProjection_mem_orthogonal v
    exact this w (W.le_topologicalClosure hw)
  have hmem : ∀ w, w ∈ eigIn W A x ↔ w ∈ W ∧ A w = (x : ℂ) • w := by
    intro w
    simp [eigIn, Module.End.mem_eigenspace_iff]
  have key : ∀ u ∈ eigIn W A x, (∀ w ∈ eigIn W A x, inner ℂ w (v - u) = 0) →
      prj (eigIn W A x) v = u := by
    intro u hu h
    refine Submodule.eq_starProjection_of_mem_orthogonal
      ((eigIn W A x).le_topologicalClosure hu) ?_
    rw [Submodule.orthogonal_closure]
    exact fun w hw => h w hw
  split_ifs with hx
  · subst hx
    exact key _ ((hmem _).2 ⟨hPW, hv⟩) fun w hw => hperp w ((hmem w).1 hw).1
  · refine key 0 (Submodule.zero_mem _) fun w hw => ?_
    obtain ⟨hwW, hwA⟩ := (hmem w).1 hw
    have h1 : inner ℂ (A w) (prj W v) = inner ℂ w (A (prj W v)) :=
      hA.isSymmetric w (prj W v)
    rw [hwA, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
    have h2 : inner ℂ w (prj W v) = 0 := by
      by_contra h0
      exact hx (by exact_mod_cast mul_right_cancel₀ h0 h1)
    have h3 := hperp w hwW
    rw [inner_sub_right, h2] at h3
    rw [inner_sub_right, inner_zero_right]
    exact h3
