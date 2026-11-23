import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullCorrBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldFlow
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

private theorem norm_hom_le {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (W : V → V) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) (v : Fin q → V) (A : F →L[ℝ] F) (K : ℝ)
    (hc : ContinuousOn (fun t => hk W t w p) (Set.Icc 0 1))
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖A (hk W t w p v)‖ ≤ K) : ‖A (hom W w p v)‖ ≤ K := by
  have hi : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1 :=
    hc.intervalIntegrable_of_Icc zero_le_one
  have e := (A.comp (ContinuousAlternatingMap.apply ℝ V F v)).intervalIntegral_comp_comm hi
  have e' : A (hom W w p v) = ∫ t in (0 : ℝ)..1, A (hk W t w p v) := e.symm
  rw [e']
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := K)
    (f := fun t => A (hk W t w p v)) fun t ht => hb t (by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact Set.Ioc_subset_Icc_self ht)
  simpa using this

theorem UpperTheory.V.Lit.Geo.homBd :
    HomBd := by
  intro E _ _ _ a ho U Ξ Y C hY W hW q
  obtain ⟨B₁, hB₁, h₁⟩ := corrBd E a U Ξ C (q + 1)
  obtain ⟨B₂, hB₂, h₂⟩ := fieldDer E a U Y C hY
  obtain ⟨B₃, hB₃, h₃⟩ := fieldBd E a U Y C hY W hW
  obtain ⟨hfl, hfe⟩ := fieldFlow E a ho U Ξ Y C hY W hW
  refine ⟨B₁ * B₂ * (B₃ * 2) ^ q, by positivity, fun α α' w hα hw hw' g M hM hb X => ?_⟩
  obtain ⟨y, x, hyx⟩ : ∃ (y : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
      (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 = infGL E a y * finGL E a x :=
    ⟨_, _, (infGL_mul_finGL _).symm⟩
  have hYg : Y (infGL E a y * finGL E a x) = Y g := by
    obtain ⟨t, ht⟩ := (retrFacts E a).1 g
    have := hY.left 1 t g
    rw [map_one, one_mul] at this
    rw [← hyx, ht, this]
  have hp : sand y (hOne E a) ∈ (geo ho U Ξ).Y := ⟨y, rfl⟩
  have e1 := hw' y x X
  rw [(omApply _ _ _ _ (geo ho U Ξ) W hfl q).2 w _ _ hp] at e1
  have e2 : ev (α' X) (infGL E a y * finGL E a x) = mulVecL (Ξ.mat y⁻¹)
      (hom (W (x : GL (Fin a) (Af E) ⧸ U)) (w.1 (x : GL (Fin a) (Af E) ⧸ U)) (sand y (hOne E a))
        fun i => (2 : ℝ) • sand y (hv (X i))) := by
    rw [e1, mulVecL_apply, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  rw [hyx, e2]
  refine norm_hom_le _ _ _ _ _ _
    ((hkSmooth _ _ _ (geo ho U Ξ).isOpen _ (hfl.field _) q _ (w.2 _).1).2.2.1 _ hp) fun t ht => ?_
  have ht' : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨h, hh, hC, hC'⟩ := hY.root g t ht'
  choose v' hv' hv'' using h₃ y x t ht'
  have key := h₁ α w.1 hα hw g y h x M hyx hC hC' hM (hb t ht h hh)
    (Matrix.vecCons (hv (Y g)) fun i => v' ((2 : ℝ) • hv (X i)))
  have e3 : (Matrix.vecCons (W (x : GL (Fin a) (Af E) ⧸ U) (sand y (hOne E a))) fun i =>
      fderiv ℝ (flow (W (x : GL (Fin a) (Af E) ⧸ U)) t) (sand y (hOne E a)) ((2 : ℝ) • sand y (hv (X i)))) =
      fun i => sand y (Matrix.vecCons (hv (Y g)) (fun i => v' ((2 : ℝ) • hv (X i))) i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Matrix.cons_val_zero]
      rw [hW y x, hYg]
    · simp only [Matrix.cons_val_succ]
      rw [← hv'', map_smul (sand y)]
  rw [mulVecL_apply, hk_apply, e3, hfe y h x t (by rw [hYg]; exact hh)]
  refine key.trans ?_
  rw [Fin.prod_univ_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  have b1 : ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ (B₃ * 2) ^ q * ∏ i, ‖hv (X i)‖ := by
    calc ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ ∏ i : Fin q, (B₃ * 2) * ‖hv (X i)‖ :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => (hv' _).trans_eq (by
            rw [norm_smul, Real.norm_ofNat, mul_assoc])
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have b2 := mul_le_mul (h₂ g).1 b1 (Finset.prod_nonneg fun _ _ => norm_nonneg _) hB₂
  calc _ ≤ B₁ * M * (B₂ * ((B₃ * 2) ^ q * ∏ i, ‖hv (X i)‖)) := mul_le_mul_of_nonneg_left b2 (mul_nonneg hB₁ hM)
    _ = _ := by ring
