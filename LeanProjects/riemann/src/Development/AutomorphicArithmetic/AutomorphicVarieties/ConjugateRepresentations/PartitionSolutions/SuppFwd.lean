import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFactsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SandCpt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.suppFwd :
    SuppFwd := by
  intro E _ _ _ a ho U hU Ξ q α w h hα
  obtain ⟨R, hR⟩ := hα
  obtain ⟨C, hC, hC'⟩ := (qhtFacts E a).2.2.2 R
  have h1 : Continuous (pInf E) := continuous_pi fun v =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).continuous.comp
      ((continuous_apply v).comp continuous_fst)
  have h2 : Continuous (pFin E) := continuous_snd
  have hi : Continuous fun g : GA E a => GeneralLinearGroup.map (pInf E) g :=
    Continuous.units_map _ (continuous_id.matrix_map h1)
  have hf : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) g :=
    Continuous.units_map _ (continuous_id.matrix_map h2)
  haveI : DiscreteTopology (GL (Fin a) (Af E) ⧸ U) := QuotientGroup.discreteTopology hU
  refine ⟨(fun g : GA E a => ((GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U)) '' C,
    (fun g : GA E a => sand (GeneralLinearGroup.map (pInf E) g) (hOne E a)) '' C,
    (hC.image (QuotientGroup.continuous_mk.comp hf)).finite_of_discrete,
    hC.image ((sandCpt E a).1.comp hi), ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact ⟨_, rfl⟩
  · rintro s _ ⟨g, rfl⟩ hp
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have hlt : R < qht (infGL E a g * finGL E a x) := by
      by_contra hle
      obtain ⟨γ, t, hm⟩ := hC' _ (not_lt.1 hle)
      obtain ⟨e1, r, hr, e2⟩ := (splitFacts E a).1 t
      refine hp ⟨⟨γ, Subgroup.mem_top γ⟩, r, hr, ⟨_, hm, ?_⟩, ⟨_, hm, ?_⟩⟩
      · simp only [map_mul, e1, pFin_infGL, pFin_finGL, one_mul, mul_one]
        rfl
      · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one, ContinuousLinearMap.mul_apply, e2, map_smul, geo_ρ]
    refine ContinuousAlternatingMap.ext fun v => ?_
    have hv' : v = fun i => (2 : ℝ) • sand g (hv (hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i)))) := by
      funext i
      rw [LinearEquiv.apply_symm_apply, map_smul, smul_smul, ← ContinuousLinearMap.mul_apply, ← map_mul,
        mul_inv_cancel, map_one]
      simp
    rw [hv', h, hR _ _ hlt, Matrix.mulVec_zero]
    rfl
