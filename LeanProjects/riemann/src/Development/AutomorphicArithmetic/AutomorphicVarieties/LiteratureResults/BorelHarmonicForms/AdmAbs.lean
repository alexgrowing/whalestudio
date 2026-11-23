import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AvgPos

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem compactSpace_unitary_matrix_pi_complex (T : Type) [Fintype T] (a : ℕ) :
    CompactSpace (unitary (Matrix (Fin a) (Fin a) (T → ℂ))) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a =>
      Set.univ.pi fun _ : T => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall 0 1
  have hof : Continuous (Matrix.of : (Fin a → Fin a → T → ℂ) → Matrix (Fin a) (Fin a) (T → ℂ)) :=
    continuous_id
  refine (hK.image hof).of_isClosed_subset isClosed_unitary ?_
  intro U hU
  refine ⟨Matrix.of.symm U, ?_, by simp⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro i j t
  have hM : U.map (fun f => f t) ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext k l
    have h : (U * star U) k l t = (1 : Matrix (Fin a) (Fin a) (T → ℂ)) k l t := by
      rw [Unitary.mul_star_self_of_mem hU]
    by_cases hkl : k = l
    · subst hkl
      simpa [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply] using h
    · simpa [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply, hkl] using h
  simpa using entry_norm_bound_of_unitary hM i j

private theorem continuous_unitary_toUnits_matrix_pi_complex (T : Type) [Fintype T] (a : ℕ) :
    Continuous (Unitary.toUnits : unitary (Matrix (Fin a) (Fin a) (T → ℂ)) →
      (Matrix (Fin a) (Fin a) (T → ℂ))ˣ) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · simpa [Function.comp_def, Unitary.val_toUnits_apply] using continuous_subtype_val
  · simp only [Unitary.val_inv_toUnits_apply]
    exact continuous_subtype_val.comp continuous_inv

private theorem conjTranspose_D_mul_add_mul_D_eq_zero_of_skew {T : Type} [Fintype T] {a d : ℕ}
    {R : GL (Fin a) (T → ℂ) →* Matrix (Fin d) (Fin d) ℂ}
    {D : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hR : IsHolRep R D) (G : Matrix (Fin d) (Fin d) ℂ)
    (hinv : ∀ U : unitary (Matrix (Fin a) (Fin a) (T → ℂ)),
      (R (Unitary.toUnits U))ᴴ * G * R (Unitary.toUnits U) = G)
    (Y : Matrix (Fin a) (Fin a) (T → ℂ)) (hY : star Y = -Y) :
    (D Y)ᴴ * G + G * D Y = 0 := by
  have hcd : ∃ c : ℝ → GL (Fin a) (T → ℂ), c 0 = 1 ∧
      (∀ s, (c s : Matrix (Fin a) (Fin a) (T → ℂ)) ∈ unitary (Matrix (Fin a) (Fin a) (T → ℂ))) ∧
      ∀ (i j : Fin a) (t : T), HasDerivAt (fun s => (c s : Matrix (Fin a) (Fin a) (T → ℂ)) i j t)
        (Y i j t) 0 := by
    letI : NormedRing (Matrix (Fin a) (Fin a) (T → ℂ)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (T → ℂ)) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℚ (Matrix (Fin a) (Fin a) (T → ℂ)) := Matrix.linftyOpNormedAlgebra
    haveI : CompleteSpace (Matrix (Fin a) (Fin a) (T → ℂ)) := FiniteDimensional.complete ℝ _
    let S : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℝ] Matrix (Fin a) (Fin a) (T → ℂ) :=
      { toFun := star
        map_add' := star_add
        map_smul' := fun r M => by simp [star_smul] }
    haveI : @ContinuousStar (Matrix (Fin a) (Fin a) (T → ℂ))
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ :=
      ⟨S.continuous_of_finiteDimensional⟩
    have hmem : ∀ s : ℝ, NormedSpace.exp (s • Y) ∈ unitary (Matrix (Fin a) (Fin a) (T → ℂ)) :=
      fun s => NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
        rw [skewAdjoint.mem_iff, star_smul, hY]
        simp)
    refine ⟨fun s => Unitary.toUnits ⟨NormedSpace.exp (s • Y), hmem s⟩, ?_, fun s => ?_, ?_⟩
    · ext1
      simp [Unitary.val_toUnits_apply]
    · simpa [Unitary.val_toUnits_apply] using hmem s
    · intro i j t
      have hexp := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
      rw [zero_smul, NormedSpace.exp_zero, one_mul] at hexp
      let L0 : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℝ] ℂ :=
        { toFun := fun M => M i j t
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let L : Matrix (Fin a) (Fin a) (T → ℂ) →L[ℝ] ℂ := ⟨L0, L0.continuous_of_finiteDimensional⟩
      exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hexp
  obtain ⟨c, hc0, hcu, hcd⟩ := hcd
  have hr := hR.der c Y hc0 hcd
  have hconst : ∀ s, (R (c s))ᴴ * G * R (c s) = G := by
    intro s
    have h := hinv ⟨c s, hcu s⟩
    have hu : Unitary.toUnits ⟨(c s : Matrix (Fin a) (Fin a) (T → ℂ)), hcu s⟩ = c s := by
      ext1
      simp [Unitary.val_toUnits_apply]
    rwa [hu] at h
  have h1 : R (c 0) = 1 := by rw [hc0, map_one]
  ext i j
  have e : ∀ s, ((R (c s))ᴴ * G * R (c s)) i j =
      ∑ l, (∑ k, star (R (c s) k i) * G k l) * R (c s) l j := by
    intro s
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hF := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
      (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
        ((hr k i).star).mul_const (G k l))).mul (hr l j))
  have hF0 : HasDerivAt (fun s => ∑ l, (∑ k, star (R (c s) k i) * G k l) * R (c s) l j) 0 0 := by
    have : (fun s => ∑ l, (∑ k, star (R (c s) k i) * G k l) * R (c s) l j) = fun _ => G i j := by
      funext s
      rw [← e, hconst]
    rw [this]
    exact hasDerivAt_const _ _
  have hu := hF.unique hF0
  rw [h1] at hu
  simp [Matrix.one_apply] at hu
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simpa [Finset.sum_add_distrib] using hu

theorem UpperTheory.V.Lit.Bor.admissible_abs_bound :
    UpperTheory.V.Lit.Bor.AdmAbs := by
  intro T _ a d R D hR
  haveI := compactSpace_unitary_matrix_pi_complex T a
  obtain ⟨G, hG, hinv⟩ := avgPos (unitary (Matrix (Fin a) (Fin a) (T → ℂ))) d
    (R.comp Unitary.toUnits) (fun i j => (hR.cont i j).comp (continuous_unitary_toUnits_matrix_pi_complex T a))
  refine ⟨G, hG, fun Z => ?_⟩
  obtain ⟨X, hXd⟩ : ∃ X : Matrix (Fin a) (Fin a) (T → ℂ), X = (1 / 2 : ℂ) • (Z - star Z) := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V : Matrix (Fin a) (Fin a) (T → ℂ),
      V = (-(Complex.I / 2)) • (Z + star Z) := ⟨_, rfl⟩
  have hX : star X = -X := by
    subst hXd
    ext i j t
    simp [Matrix.star_apply]
    ring
  have hV : star V = -V := by
    subst hVd
    ext i j t
    simp [Matrix.star_apply]
    ring
  have hZ : Z = X + Complex.I • V := by
    subst hXd hVd
    ext i j t
    simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have hsZ : star Z = -X + Complex.I • V := by
    subst hXd hVd
    ext i j t
    simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have eX : (D X)ᴴ * G = -(G * D X) :=
    eq_neg_of_add_eq_zero_left (conjTranspose_D_mul_add_mul_D_eq_zero_of_skew hR G hinv X hX)
  have eV : (D V)ᴴ * G = -(G * D V) :=
    eq_neg_of_add_eq_zero_left (conjTranspose_D_mul_add_mul_D_eq_zero_of_skew hR G hinv V hV)
  have hDZ : D Z = D X + Complex.I • D V := by
    conv_lhs => rw [hZ]
    rw [map_add, map_smul]
  rw [hDZ, hsZ, map_add, map_neg, map_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.add_mul, Matrix.smul_mul, eX, eV, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul]
  simp [Complex.star_def]
