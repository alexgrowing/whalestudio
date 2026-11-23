import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem
import Development.AutomorphicArithmetic.CommutativeAlgebra.PicUnit
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteEtaleFaithfullyFlatCoverOfEtaleLocal
import Development.AutomorphicArithmetic.CommutativeAlgebra.SectionsSpecPiBijectiveProdSections
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUniqueSectionOfEtaleFaithfullyFlatDescent

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private lemma sec_res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (a : Sec F U) : Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  change (ModuleCat.Hom.hom (F.obj.map k.op)) ((ModuleCat.Hom.hom (F.obj.map g.op)) a) = (ModuleCat.Hom.hom (F.obj.map (k ≫ g).op)) a
  rw [op_comp, Functor.map_comp]
  rfl

private lemma sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (a : Sec F U) : Sec.map φ (Sec.res g a) = Sec.res g (Sec.map φ a) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun f => f.hom a) h

theorem UpperTheory.multiplicativeGroup_oneCocycle_etaleLocally_coboundary :
    ∀ (A : Type) [CommRing A] (z : Sec ((res ℤ Gm).X 1) (Spec (CommRingCat.of A))),
        Sec.map ((res ℤ Gm).d 1 2) z = 0 →
        ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C), Module.FaithfullyFlat A C ∧ Algebra.Etale A C ∧
          ∃ w : Sec ((res ℤ Gm).X 0) (Spec (CommRingCat.of C)),
            Sec.map ((res ℤ Gm).d 0 1) w = Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) z := by
  intro A _ z hz
  have hloc := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm (Spec (CommRingCat.of A))).2.2.1 0 1 2 (by norm_num) (by norm_num) z (by norm_num) hz
  have hstab : ∀ (V W : Scheme) (g : V ⟶ Spec (CommRingCat.of A)) (k : W ⟶ V),
      (∃ y, Sec.map ((res ℤ Gm).d 0 1) y = Sec.res g z) →
      (∃ y, Sec.map ((res ℤ Gm).d 0 1) y = Sec.res (k ≫ g) z) := by
    rintro V W g k ⟨y, hy⟩
    exact ⟨Sec.res k y, by rw [sec_map_res, hy, sec_res_res]⟩
  obtain ⟨n, C, hC, hA, het, hff, hP⟩ := UpperTheory.exists_finite_etale_faithfullyFlat_cover_of_etaleLocal_affine A _ hstab hloc
  obtain ⟨w, hw⟩ := (UpperTheory.sections_specPi_bijective_prod_sections ℤ ((res ℤ Gm).X 0) n C).2 (fun i => (hP i).choose)
  refine ⟨(i : Fin n) → C i, inferInstance, inferInstance, hff, het, w, ?_⟩
  apply (UpperTheory.sections_specPi_bijective_prod_sections ℤ ((res ℤ Gm).X 1) n C).1
  funext i
  have hwi := congrFun hw i
  dsimp only at hwi
  show Sec.res _ (Sec.map _ w) = Sec.res _ (Sec.res _ z)
  rw [← sec_map_res, hwi, (hP i).choose_spec, sec_res_res, ← Spec.map_comp]
  rfl
