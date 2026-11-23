import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem real_unitary_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (∀ z : Fin n → ℝ, Reduction.euclidNorm (z ᵥ* M) = Reduction.euclidNorm z) ↔ M ∈ unitaryGroup (Fin n) ℝ := by
  refine ⟨fun h => ?_, fun h z => Reduction.euclidNorm_vecMul_unitary h z⟩
  have hq : ∀ z : Fin n → ℝ, (z ᵥ* M) ⬝ᵥ (z ᵥ* M) = z ⬝ᵥ z := by
    intro z
    have := h z
    rw [Reduction.euclidNorm, Reduction.euclidNorm, Real.sqrt_inj (by positivity) (by positivity)] at this
    simp only [Real.norm_eq_abs, sq_abs] at this
    simpa only [dotProduct, sq] using this
  have hb : ∀ x z : Fin n → ℝ, (x ᵥ* M) ⬝ᵥ (z ᵥ* M) = x ⬝ᵥ z := by
    intro x z
    have h1 := hq (x + z)
    rw [add_vecMul] at h1
    simp only [add_dotProduct, dotProduct_add, hq] at h1
    rw [dotProduct_comm (z ᵥ* M), dotProduct_comm z x] at h1
    linarith
  rw [mem_unitaryGroup_iff]
  ext i j
  have := hb (Pi.single i 1) (Pi.single j 1)
  rw [single_one_vecMul, single_one_vecMul, single_one_dotProduct] at this
  rw [mul_apply, one_apply]
  simp only [star_apply, star_trivial]
  refine Eq.trans this ?_
  simp [Pi.single_apply]

private theorem pi_unitary_iff {ι : Type} {n : ℕ} (M : Matrix (Fin n) (Fin n) (ι → ℝ)) :
    M ∈ unitaryGroup (Fin n) (ι → ℝ) ↔ ∀ w, M.map (fun x => x w) ∈ unitaryGroup (Fin n) ℝ := by
  simp only [mem_unitaryGroup_iff, ← Matrix.ext_iff, funext_iff, mul_apply, one_apply, star_apply, map_apply,
    Finset.sum_apply, Pi.mul_apply, Pi.star_apply, ite_apply, Pi.one_apply, Pi.zero_apply]
  exact ⟨fun h w i j => h i j w, fun h i j w => h w i j⟩

private theorem infAt_grpEq {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}
    (y : GL (Fin a) (TR.Rinf E)) (w : InfinitePlace E) (i j : Fin a) :
    (Reduction.infAt w (infEmb E a (grpEq E a y)) : Matrix (Fin a) (Fin a) w.Completion) i j =
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (y.val i j w) := by
  rw [infEmb_grpEq]
  have h := congrArg (fun g : GL (Fin a) (TR.Rinf E) => TR.infEq E (g.val i j) w) (TR.pInf_infGL y)
  refine Eq.trans ?_ h
  exact (congrFun ((TR.infEq E).apply_symm_apply ((TR.infGL E a y).val i j).1) w).symm

theorem UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces :
    UpperTheory.V.Fb.CptIff := by
  intro E _ _ _ a y
  change infEmb E a (grpEq E a y) ∈ Reduction.maxCompact (K := E) (n := a) ↔ _
  have hf : ∀ v, Reduction.finAt v (infEmb E a (grpEq E a y)) ∈ GLnLocal.integralGL (v.adicCompletion E) a := by
    intro v
    have : Reduction.finAt v (infEmb E a (grpEq E a y)) = 1 := by
      show (AdelicGLn.finiteRestrictedEquiv E a (AdelicGLn.prodEquiv E a (infEmb E a (grpEq E a y))).2) v = 1
      rw [prodEquiv_infEmb, map_one]
      rfl
    rw [this]
    exact one_mem _
  rw [Reduction.mem_maxCompact, and_iff_left hf, pi_unitary_iff]
  refine forall_congr' fun w => ?_
  rw [Reduction.mem_archCompact, ← real_unitary_iff]
  set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) with hψdef
  have hψ : ∀ z, ‖ψ.toRingHom z‖ = ‖z‖ := fun z =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero
      (map_zero _) z
  have e : ∀ z : Fin a → w.Completion,
      (fun j => ψ.toRingHom ((z ᵥ* (Reduction.infAt w (infEmb E a (grpEq E a y)) : Matrix (Fin a) (Fin a) w.Completion)) j)) =
        (fun i => ψ.toRingHom (z i)) ᵥ* y.val.map (fun x => x w) := by
    intro z
    ext j
    simp only [vecMul, dotProduct, map_sum, map_mul, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [infAt_grpEq]
    exact congrArg _ (ψ.apply_symm_apply _)
  constructor
  · intro h z
    have hz : z = fun i => ψ.toRingHom (ψ.symm (z i)) := funext fun i => (ψ.apply_symm_apply _).symm
    rw [hz, ← e, Reduction.euclidNorm_map _ hψ, Reduction.euclidNorm_map _ hψ, h]
  · intro h z
    rw [← Reduction.euclidNorm_map _ hψ, e, h, Reduction.euclidNorm_map _ hψ]
