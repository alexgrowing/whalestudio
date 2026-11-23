import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem exp_block_extension (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n) (Y : ArchMatrix K a) :
    (1 : ArchMatrix K n) + (show ArchMatrix K n from ext0 (R := mixedSpace K) e (NormedSpace.exp Y - 1 : ArchMatrix K a)) =
      NormedSpace.exp (show ArchMatrix K n from ext0 (R := mixedSpace K) e Y) := by
  have hsm : ∀ (c : ℝ) (Z : Matrix (Fin a) (Fin a) (mixedSpace K)), ext0 e (c • Z) = c • ext0 e Z := by
    intro c Z
    simp only [ext0, Matrix.mul_smul, Matrix.smul_mul]
  let g : ArchMatrix K a →ₗ[ℝ] ArchMatrix K n :=
    { toFun := fun X => ext0 (R := mixedSpace K) e X
      map_add' := fun X Z => matrixExtendByZero_add e X Z
      map_smul' := fun c X => hsm c X }
  have hg : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have hpow : ∀ k : ℕ, (g Y) ^ (k + 1) = g (Y ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ Y (k + 1)]
      exact matrixExtendByZero_mul e _ _
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) Y).map g hg
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (g Y)
  have h3 : HasSum (fun k : ℕ => if k = 0 then (1 - g 1 : ArchMatrix K n) else 0) (1 - g 1) :=
    hasSum_ite_eq 0 _
  have h4 := h1.add h3
  have heq : (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • (g Y) ^ k) =
      fun k : ℕ => g (((k.factorial : ℝ)⁻¹) • Y ^ k) + if k = 0 then (1 - g 1) else 0 := by
    funext k
    cases k with
    | zero => simp
    | succ k => rw [if_neg (Nat.succ_ne_zero k), add_zero, map_smul, hpow]
  rw [heq] at h2
  have h5 := h2.unique h4
  have hsub : g (NormedSpace.exp Y - 1) = g (NormedSpace.exp Y) - g 1 := map_sub g _ _
  change (1 : ArchMatrix K n) + g (NormedSpace.exp Y - 1) = NormedSpace.exp (g Y)
  rw [hsub, h5]
  abel

private theorem UpperTheory.prodEquiv_apply_eq_map_fst_snd (K : Type) [Field K] [NumberField K] (m : ℕ)
    (g : AdelicGLn.AdelicGL K m) :
    AdelicGLn.prodEquiv K m g =
      (GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g,
        GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g) := by
  ext i j <;> rfl

private theorem UpperTheory.archEquiv_symm_apply_eq_map_mixedSpace (K : Type) [Field K] [NumberField K] (m : ℕ) (x : archGroup K m) :
    (archEquiv K m).symm x =
      GeneralLinearGroup.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom
        (show GL (Fin m) (mixedSpace K) from (x : (ArchMatrix K m)ˣ)) := by
  ext i j
  rfl

theorem UpperTheory.blockEmbedding_comm_infEmb_and_exp :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n), (∀ x, emb e (infEmb K a x) = infEmb K n (embArch e x)) ∧ ∀ Y : Matrix (Fin a) (Fin a) (mixedSpace K), embArch e ((isExpLieAlgebra K a).expG ((isExpLieAlgebra K a).ofLie (toLie K a Y))) = (isExpLieAlgebra K n).expG ((isExpLieAlgebra K n).ofLie (toLie K n (ext0 e Y))) := by
  intro K _ _ a n e
  refine ⟨fun x => ?_, fun Y => ?_⟩
  · apply (AdelicGLn.prodEquiv K n).injective
    have hx := prodEquiv_infEmb (K := K) (n := a) x
    rw [UpperTheory.prodEquiv_apply_eq_map_fst_snd] at hx
    rw [Prod.mk.injEq] at hx
    rw [UpperTheory.prodEquiv_apply_eq_map_fst_snd, prodEquiv_infEmb]
    refine Prod.ext ?_ ?_
    · refine (emb_map e (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
        (infEmb K a x)).trans ((congrArg (emb e) hx.1).trans ?_)
      rw [UpperTheory.archEquiv_symm_apply_eq_map_mixedSpace, UpperTheory.archEquiv_symm_apply_eq_map_mixedSpace]
      exact (emb_map e _ _).symm
    · exact (emb_map e (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
        (infEmb K a x)).trans ((congrArg (emb e) hx.2).trans (map_one _))
  · apply Subtype.ext
    apply Units.ext
    exact exp_block_extension K e Y
