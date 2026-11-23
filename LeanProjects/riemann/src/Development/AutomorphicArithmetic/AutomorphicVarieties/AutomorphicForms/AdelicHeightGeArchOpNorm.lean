import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem loc_le_height {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GA E a) (w : InfinitePlace E) :
    locHeight (Reduction.infAt w g) ≤ AutomorphicForm.height g := by
  classical
  have h1 : locHeight (Reduction.infAt w g) ≤ locHeight (Reduction.infAt w g) ^ w.mult :=
    le_self_pow₀ (one_le_locHeight _) InfinitePlace.mult_pos.ne'
  have h2 : locHeight (Reduction.infAt w g) ^ w.mult ≤
      ∏ w : InfinitePlace E, locHeight (Reduction.infAt w g) ^ w.mult := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
    refine le_mul_of_one_le_right (pow_nonneg (locHeight_pos _).le _) ?_
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
      (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl fun _ _ => one_le_pow₀ (one_le_locHeight _)
  exact h1.trans (h2.trans (le_mul_of_one_le_right (zero_le_one.trans (one_le_prod_locHeight g))
    (one_le_finprod_locHeight g)))

private theorem norm_le_height {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ} (g : GA E a) :
    ‖TR.toL (GeneralLinearGroup.map (TR.pInf E) g).val‖ ≤ AutomorphicForm.height g := by
  have h0 : 0 ≤ AutomorphicForm.height g := (height_pos g).le
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
    (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
  refine le_trans (le_of_eq ?_) ((norm_apply_le_locHeight _ i j).trans (loc_le_height g w))
  have hi := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).isometry
  exact hi.norm_map_of_map_zero
    (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w))) ((g.val i j).1 w)

theorem UpperTheory.adelicHeight_ge_archOpNorm :
    UpperTheory.V.Fb.HeightGe := by
  intro E _ _ _ a g
  have h1 := norm_le_height g
  have h2 := norm_le_height g⁻¹
  rw [height_inv, map_inv] at h2
  have h3 := one_le_height g
  unfold TR.height
  linarith
