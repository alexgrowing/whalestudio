import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.UMeasEx
import Development.AutomorphicArithmetic.AdelicSL2.IsOpenEmbeddingProjection
import Development.AutomorphicArithmetic.AdelicSL2.ExistsHaarRestrictRangeSl2IdeleMapEqSmulProd
import Development.AutomorphicArithmetic.AdelicSL2.IsFundamentalDomainImageSl2DomainProdIdeles

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical
open scoped ENNReal NNReal

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.fibre :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fibre := by
  intro M μ _ Φ hΦ h0
  obtain ⟨U⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.uMeasEx_of
  haveI := M.haar
  have hemb : MeasurableEmbedding pm := UpperTheory.isOpenEmbedding_projection.measurableEmbedding
  set F : Set GG := pm '' (M.D ×ˢ Set.univ) with hFdef
  have hF : IsFundamentalDomain Ga F μ := UpperTheory.isFundamentalDomain_image_sl2Domain_prod_ideles M U μ
  have hFm : MeasurableSet F := hemb.measurableSet_image.2 (M.meas.prod MeasurableSet.univ)
  have hinv : ∀ (γ : Ga) (x : GG), Φ ((γ • x : GG) : GL (Fin 2) (A ℚ)) = Φ (x : GL (Fin 2) (A ℚ)) := by
    intro γ x
    obtain ⟨r, hr⟩ : ∃ r : GL (Fin 2) ℚ, ratGL ℚ 2 r = ((γ : GG) : GL (Fin 2) (A ℚ)) := by
      obtain ⟨r, hr⟩ := γ.2
      exact ⟨r, hr⟩
    have := hΦ.left r (x : GL (Fin 2) (A ℚ))
    rw [hr] at this
    exact this
  let Φq : GroundTheory.Automorphic.RightCosetSpace Ga → ℂ := fun y => Φ ((Quotient.out y : GG) : GL (Fin 2) (A ℚ))
  have hq : ∀ x : GG, Φq (GroundTheory.Automorphic.RightCosetSpace.mk Ga x) = Φ (x : GL (Fin 2) (A ℚ)) := by
    intro x
    have h : GroundTheory.Automorphic.RightCosetSpace.mk Ga (Quotient.out (GroundTheory.Automorphic.RightCosetSpace.mk Ga x)) =
        GroundTheory.Automorphic.RightCosetSpace.mk Ga x := Quotient.out_eq _
    obtain ⟨γ, hγ⟩ := GroundTheory.Automorphic.RightCosetSpace.mk_eq_mk_iff.1 h
    change Φ ((Quotient.out (GroundTheory.Automorphic.RightCosetSpace.mk Ga x) : GG) : GL (Fin 2) (A ℚ)) = _
    rw [← hγ, hinv]
  have hqc : Continuous Φq := by
    refine (GroundTheory.Automorphic.RightCosetSpace.isOpenQuotientMap_mk (Γ := Ga)).isQuotientMap.continuous_iff.2 ?_
    have : Φq ∘ GroundTheory.Automorphic.RightCosetSpace.mk Ga = fun x : GG => Φ (x : GL (Fin 2) (A ℚ)) := funext hq
    rw [this]
    exact hΦ.cont.comp continuous_subtype_val
  change ∫ y, Φq y ∂(GroundTheory.Automorphic.RightCosetSpace.quotientMeasure Ga μ) = 0
  rw [← GroundTheory.Automorphic.RightCosetSpace.map_restrict_eq_quotientMeasure μ hF,
    integral_map (GroundTheory.Automorphic.RightCosetSpace.measurable_mk Ga).aemeasurable hqc.aestronglyMeasurable]
  simp only [hq]
  obtain ⟨c, hc⟩ := UpperTheory.exists_haar_restrict_range_sl2IdeleMap_eq_smul_prod M U μ
  have hFR : F ⊆ Set.range pm := Set.image_subset_range _ _
  have hres : μ.restrict F = (c • (M.μ.prod (us U)).map pm).restrict F := by
    rw [← hc, Measure.restrict_restrict hFm, Set.inter_eq_self_of_subset_left hFR]
  rw [hres, Measure.restrict_smul, integral_smul_nnreal_measure, hemb.setIntegral_map]
  have hpre : pm ⁻¹' F = M.D ×ˢ Set.univ := hemb.injective.preimage_image _
  have hr : (M.μ.prod (us U)).restrict (M.D ×ˢ Set.univ) = (M.μ.restrict M.D).prod (us U) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hpre, hr]
  by_cases hi : Integrable (fun x : G1 ℚ × US => Φ (pm x : GL (Fin 2) (A ℚ))) ((M.μ.restrict M.D).prod (us U))
  · rw [integral_prod_symm _ hi]
    have : ∀ t : US, ∫ g in M.D, Φ (pm (g, t) : GL (Fin 2) (A ℚ)) ∂M.μ = 0 := fun t => h0 t t.2
    simp [this]
  · rw [integral_undef hi, smul_zero]
