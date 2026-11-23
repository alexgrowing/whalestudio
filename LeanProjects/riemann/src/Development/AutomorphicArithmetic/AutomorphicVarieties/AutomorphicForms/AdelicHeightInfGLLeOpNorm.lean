import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem ent (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (y : GL (Fin a) (TR.Rinf E))
    (w : InfinitePlace E) (i j : Fin a) :
    ‖(Reduction.infAt w (TR.infGL E a y) : Matrix (Fin a) (Fin a) w.Completion) i j‖ ≤ ‖TR.toL y.val‖ := by
  have h := congrArg (fun g : GL (Fin a) (InfiniteAdeleRing E) => g.val i j w)
    (map_cornerGL_of_hom (TR.sInf E) (RingHom.fst (InfiniteAdeleRing E) (Af E))
      (TR.infEq E).toRingHom (fun _ => rfl) y)
  have e : (Reduction.infAt w (TR.infGL E a y) : Matrix (Fin a) (Fin a) w.Completion) i j =
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (y.val i j w) := h
  have e0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 = 0 :=
    map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
  rw [e, (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.isometry.norm_map_of_map_zero e0]
  exact (norm_le_pi_norm (y.val i j) w).trans
    ((norm_le_pi_norm (TR.toL y.val i) j).trans (norm_le_pi_norm (TR.toL y.val) i))

private theorem finOne (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (y : GL (Fin a) (TR.Rinf E))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) : Reduction.finAt v (TR.infGL E a y) = 1 := by
  have h1 : Reduction.finAt v (TR.infGL E a y) = Reduction.finAt v (1 : AdelicGLn.AdelicGL E a) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h := congrArg (fun g : GL (Fin a) (Af E) => g.val i j v)
      ((TR.pFin_infGL y).trans (map_one (GeneralLinearGroup.map (n := Fin a) (pFin E))).symm)
    exact h
  rw [h1, Reduction.finAt_one]

theorem UpperTheory.adelicHeight_infGL_le_opNorm :
    UpperTheory.V.Fb.HeightLe := by
  intro E _ _ _ a
  refine ⟨∑ w : InfinitePlace E, w.mult, fun y => ?_⟩
  have n1 := norm_nonneg (TR.toL y.val)
  have n2 := norm_nonneg (TR.toL (y⁻¹).val)
  unfold AutomorphicForm.height
  rw [finprod_eq_one_of_forall_eq_one fun v => by rw [finOne, locHeight_one], mul_one,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun w _ => (pow_pos (locHeight_pos _) _).le) fun w _ =>
    pow_le_pow_left₀ (locHeight_pos _).le ?_ _
  unfold TR.height
  refine locHeight_le (by linarith) (fun i j => ?_) fun i j => ?_
  · have := ent E a y w i j
    linarith
  · have := ent E a y⁻¹ w i j
    rw [map_inv, Reduction.infAt_inv] at this
    linarith
