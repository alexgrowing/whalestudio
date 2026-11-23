import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private lemma sec_res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (a : Sec F U) : Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

private lemma cover_loc (A C : Type) [CommRing A] [CommRing C] [Algebra A C]
    [Module.FaithfullyFlat A C] [Algebra.Etale A C] :
    Loc (Spec (CommRingCat.of A)) (fun V g => ∃ h : V ⟶ Spec (CommRingCat.of C),
      h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = g) := by
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover]
  · intro x
    have hff : (CommRingCat.ofHom (algebraMap A C)).hom.FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
    have hs := ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap A C))).mpr hff).2
    have het : Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
    obtain ⟨y, hy⟩ := hs.surj x
    exact ⟨_, Spec.map (CommRingCat.ofHom (algebraMap A C)), inferInstance, het, ⟨y, hy⟩, 𝟙 _,
      Category.id_comp _⟩
  · rintro V W g k ⟨h, rfl⟩
    exact ⟨k ≫ h, Category.assoc _ _ _⟩

private lemma lift_wd {R : Type} [CommRing R] (F : Shv R) (A C : Type) [CommRing A] [CommRing C] [Algebra A C]
    (w : Sec F (Spec (CommRingCat.of C)))
    (hw : Sec.res (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] C).toRingHom)) w =
          Sec.res (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom)) w)
    {V : Scheme.{0}} (h h' : V ⟶ Spec (CommRingCat.of C))
    (e : h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = h' ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) :
    Sec.res h w = Sec.res h' w := by
  set ψ := pullback.lift h h' e ≫ (pullbackSpecIso A C C).hom with hψ
  have hL : ψ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] C).toRingHom) = h := by
    rw [hψ, Category.assoc]
    erw [pullbackSpecIso_hom_fst]
    exact pullback.lift_fst _ _ _
  have hR : ψ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom) = h' := by
    rw [hψ, Category.assoc]
    erw [pullbackSpecIso_hom_snd]
    exact pullback.lift_snd _ _ _
  rw [← hL, ← hR, ← sec_res_res, hw, sec_res_res]

theorem UpperTheory.existsUnique_section_of_etale_faithfullyFlat_descent :
    ∀ (R : Type) [CommRing R] (F : Shv R) (A C : Type) [CommRing A] [CommRing C] [Algebra A C]
        [Module.FaithfullyFlat A C] [Algebra.Etale A C] (w : Sec F (Spec (CommRingCat.of C))),
        Sec.res (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] C).toRingHom)) w =
          Sec.res (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom)) w →
        ∃! y : Sec F (Spec (CommRingCat.of A)), Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) y = w := by
  intro R _ F A C _ _ _ _ _ w hw
  obtain ⟨S, hS, hSP⟩ := cover_loc A C
  choose lf hlf using hSP
  obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue R F _).2 S hS (fun V g hg => Sec.res (lf V g hg) w) (by
    intro V W g k hg
    rw [sec_res_res]
    apply lift_wd F A C w hw
    rw [Category.assoc, hlf, hlf])
  have hex : Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) a = w := by
    apply (GlobalTheory.T.etaleSheafSections_ext_and_glue R F _).1
    have hloc : Loc (Spec (CommRingCat.of C))
        (fun V g => S.arrows (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) :=
      GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.1 _ _ _ (fun V g => S.arrows g) ⟨S, hS, fun _ _ h => h⟩
    refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 _ _ _ hloc ?_
    intro V g hg
    rw [sec_res_res, ha V _ hg]
    exact lift_wd F A C w hw _ _ (hlf _ _ _)
  refine ⟨a, hex, ?_⟩
  intro y hy
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue R F _).1
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 _ _ _ (cover_loc A C) ?_
  rintro V g ⟨h, rfl⟩
  rw [← sec_res_res, ← sec_res_res, hy, hex]
