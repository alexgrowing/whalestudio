import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelMat
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfOf
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ValFUnitNeZero
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MulEqOneOfComb
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ValFFromSpecStalk
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open PositivityTheory.UnitarySelfGeneration.UnitProductCombination

theorem PositivityTheory.UnitarySelfGeneration.height_bound_of_chowFormHeight : PositivityTheory.UnitarySelfGeneration.ChowFormHeight → Hypotheses2 → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) := by
  intro HP hP K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s t a _ _ _ _ hW hG hd hM ha
  obtain ⟨pt, h1, h2, h3, h4⟩ := exists_pt p ψ hM.bij hM.base
  have := GlobalTheory.CommonModel.isProper_of_isProjOver hM.arith.isProjOver
  let M : GlobalTheory.ZH.RatModel (𝓞 K) Ω :=
    { Z := X, s := p, sep := inferInstance, lft := inferInstance, qc := inferInstance, pt := pt, pt_s := h1,
      gen := h2, onto := h3 }
  obtain ⟨N, n, b, g, A, c, gw, hF, hgw, hcb, hφ⟩ := hM.fs
  obtain ⟨Mt, hdet, hcc, hMt⟩ := PositivityTheory.Xgn.t_xgz_height_r_vol_up_model_mat K V Nm W N n b g A hF
  obtain ⟨e, he, hv, hs, hdiv⟩ := gen_all M L.B L.isLB ev W s
    (fun w w' i hi => by
      obtain ⟨z, hz⟩ := hi
      have hg := GlobalTheory.Cartier.gen_mem (X := X) hz
      refine hM.bij.1 ?_
      rw [map_mul, map_mul]
      exact (congrArg _ (h4 _ hg _)).trans ((hM.ratio w w' i hg).trans (congrArg _ (h4 _ hg _).symm)))
    hM.bpf hG.1 hW gw (by simp only [hgw]; exact hF.span)
  have h5 := PositivityTheory.UnitarySelfGeneration.vuself_gen HP hP K V Ω Nm W ev D N n b g A t hF hG hd M (by simpa only [hgw] using hdiv)
    hM.arith L.B L.isLB e he (fun k => s (gw k)) (fun k => hgw k ▸ hv (gw k)) hs Mt hdet hcc hMt
  have h6 := (isometric_fs M L ev s hv hW b g A c gw hgw hcb hφ hs Mt hdet hcc hMt t).isSelfInter hM.arith h5
  rw [ha.unique hM.arith h6]
  exact le_of_eq (by ring)
