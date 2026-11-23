import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.DerivSimilitudeCharAtOneEqTrace
open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Bor

private theorem taylor_two {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : V → ℝ} {x : V}
    (hf : ContDiffAt ℝ 2 f x) : ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ y : V, ‖y‖ ≤ ε →
      |f (x + y) - f x - fderiv ℝ f x y| ≤ C * ‖y‖ ^ 2 := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have h2 : ∀ᶠ z in nhds x, DifferentiableAt ℝ f z :=
    (hf.eventually (by simp)).mono fun z hz => hz.differentiableAt (by simp)
  obtain ⟨ε, hε, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem ht h2)
  refine ⟨K, ε, K.2, hε, fun y hy => ?_⟩
  have hsub : Metric.closedBall x ‖y‖ ⊆ Metric.closedBall x ε := Metric.closedBall_subset_closedBall hy
  have hx : x ∈ Metric.closedBall x ‖y‖ := Metric.mem_closedBall_self (norm_nonneg _)
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ) (f := f) (f' := fderiv ℝ f)
    (φ := fderiv ℝ f x) (C := K * ‖y‖) (s := Metric.closedBall x ‖y‖) (x := x) (y := x + y)
    (fun z hz => (hb (hsub hz)).2.hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => by
      have := hK.norm_sub_le (hb (hsub hz)).1 (hb (hsub hx)).1
      refine this.trans (mul_le_mul_of_nonneg_left ?_ K.2)
      rwa [← dist_eq_norm])
    (convex_closedBall _ _) hx (by simp)
  rw [add_sub_cancel_left, Real.norm_eq_abs] at key
  calc _ ≤ _ := key
    _ = _ := by ring

theorem UpperTheory.second_order_taylor_remainder_bound :
    ScTaylor := by
  intro E _ _ a
  obtain ⟨hs, h1, hd, -⟩ := UpperTheory.deriv_similitudeChar_at_one_eq_trace E a
  have hat : ContDiffAt ℝ 2 (fun y : Lie E a => sc (Matrix.of y)) (oneL E a) :=
    (hs.contDiffAt (isOpen_invSet.mem_nhds (val_mem_invSet 1))).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  obtain ⟨C, ε, hC, hε, h⟩ := taylor_two hat
  refine ⟨C, ε, hC, hε, fun Y hY => ?_⟩
  have := h (toL Y) hY
  rw [hd, sub_neg_eq_add] at this
  have e : sc (Matrix.of (oneL E a)) = 1 := h1
  rw [e] at this
  exact this
