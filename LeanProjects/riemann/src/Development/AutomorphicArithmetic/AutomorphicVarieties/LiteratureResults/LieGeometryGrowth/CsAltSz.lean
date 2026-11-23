import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ApplySmooth
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

private theorem sz_ball {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (hf : ContDiff ℝ ∞ f) (k : ℕ) (c : ℝ) :
    ∃ C : ℝ, ∀ x : X, ‖x‖ ≤ c → Sz k f x C := by
  have hc : Continuous fun x => ∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i f x‖ :=
    continuous_finsetSum _ fun i _ => (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : X) c).bddAbove_image hc.continuousOn
  refine ⟨C, fun x hx i hi => ?_⟩
  refine le_trans ?_ (hC ⟨x, mem_closedBall_zero_iff.2 hx, rfl⟩)
  exact Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i f x‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

private theorem alt_fin (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q : ℕ) : FiniteDimensional ℝ (V [⋀^Fin q]→L[ℝ] F) := by
  let b := Module.finBasis ℝ V
  let E : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F) :=
    { toFun := fun a k => a fun i => b (k i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective E fun a a' h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact Module.Basis.ext_alternating b fun k _ => congrFun h k

theorem UpperTheory.V.Lit.Geo.Cs.altSz :
    AltSz := by
  intro V F _ _ _ _ _ _ q k c
  have h : ContDiff ℝ ∞ (fun L : V →L[ℝ] V => (ContinuousAlternatingMap.compContinuousLinearMapCLM L :
      (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F))) := by
    haveI := alt_fin V F q
    rw [contDiff_clm_apply_iff]
    intro w
    rw [contDiff_iff_contDiffAt]
    intro L
    refine UpperTheory.V.Lit.Dr.altSmooth _ V F q _ L fun v => ?_
    exact UpperTheory.V.Lit.Dr.applySmooth (V →L[ℝ] V) V F q (fun _ => w) (fun i L => L (v i)) L contDiffAt_const
      fun i => (contDiffAt_id.clm_apply contDiffAt_const)
  exact ⟨h, sz_ball _ h k c⟩
