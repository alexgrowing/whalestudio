import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.AutomorphicArithmetic.WhittakerHecke.SurjectiveEvalCoordBlowupSubstPushoutOfFlat
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsAffineBlowupCoordinateChartCover
import Development.AutomorphicArithmetic.WhittakerHecke.IsAffineOpenImagePullbackOpenImmersionChart
import Development.AutomorphicArithmetic.WhittakerHecke.IdealSheafComapEqSpecIdealSheafOfEqMap

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open FunctorialResolution.Blowup FunctorialResolution.EmbeddedResolution

theorem UpperTheory.Gal.KunnethLefschetz.G.bChartEx :
    UpperTheory.Gal.KunnethLefschetz.G.BChartEx := by
  intro R _ X W π I hπ N D A _ φ hφ hI
  classical
  set J : Ideal (MvPolynomial (Fin D) A) := coordIdeal A Finset.univ with hJ
  have hIJ : I.ideal N = Ideal.map φ J := by
    rw [show I.ideal N = _ from hI, hJ, coordIdeal_eq_span, Ideal.map_span, Finset.coe_univ,
      Set.image_univ, ← Set.range_comp]
    rfl
  have hcomap := UpperTheory.idealSheaf_comap_eq_specIdealSheaf_of_eq_map I N J φ hIJ
  haveI hfl : Flat ((IsAffineOpen.isoSpec N.2).hom ≫ Spec.map (CommRingCat.ofHom φ)) := by
    have h2 : Flat (Spec.map (CommRingCat.ofHom φ)) := Flat.SpecMap_iff.2 hφ
    exact MorphismProperty.comp_mem @Flat _ _ inferInstance h2
  have hres := hπ.restrict N.1
  rw [hcomap] at hres
  obtain ⟨q, -, hpb⟩ :=
    (isBlowupAlongIdealSheaf_affineBlowup_toSpec J).exists_isPullback_of_flat _ hres
  obtain ⟨c, hc, hcomp, hcov, hint⟩ := UpperTheory.exists_affineBlowup_coordinate_chart_cover A D
  haveI := hc
  have key := fun j => UpperTheory.isAffineOpen_image_pullback_openImmersion_chart (Over.Hom.left π) N.1 N.2 φ (AffineBlowup.toSpec J) q hpb
      (coordBlowupSubst A Finset.univ j).toRingHom (c j) (hcomp j)
  choose haff hle ρ hpush hbo using key
  have hy : ∀ j, (fun k => ρ j (if k = j then 1 else MvPolynomial.X k)) =
      fun k => if k = j then 1 else ρ j (MvPolynomial.X k) := by
    intro j
    funext k
    split_ifs <;> simp
  have alg := fun j => UpperTheory.surjective_eval_coordBlowupSubst_pushout_of_flat φ hφ j (Scheme.Hom.appLE (Over.Hom.left π) N.1 _ (hle j)).hom
    (ρ j) (hpush j)
  refine ⟨{ V := fun j => (Over.Hom.left π ⁻¹ᵁ N.1).ι ''ᵁ q ⁻¹ᵁ (c j).opensRange
            aff := haff
            le := hle
            cov := ?_
            y := fun j k => ρ j (if k = j then 1 else MvPolynomial.X k)
            surj := fun j => ?_
            ker := fun j => ?_
            inter := fun j k => hbo j _ _ (hint j k)
            nzd := fun j => (alg j).2.2 }⟩
  · apply le_antisymm (iSup_le hle)
    intro x hx
    have hmem : q ⟨x, hx⟩ ∈ ⨆ j, (c j).opensRange := by
      rw [hcov]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, ⟨x, hx⟩, hj, rfl⟩
  · rw [hy j]
    exact (alg j).1
  · rw [hy j]
    exact (alg j).2.1
