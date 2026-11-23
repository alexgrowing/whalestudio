import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianSStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyTwoEqZeroOfIsInitial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverBaseChangeComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulResidueFibreClassOfPullbackEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionElementMulZeroClassEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFibreClassEqZeroOfSmulPullbackEqZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.AbCoh.StepPrim

theorem pO1_comp {R : Type} [CommRing R] {X Y Z : Over (Sp R)} (f : X ⟶ Y) (g : Y ⟶ Z) (a : HO1 Z.hom) :
    pO1 (f ≫ g) a = pO1 f (pO1 g a) :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) g.left (ovw g) R X.left X.hom
    (RingHom.id R) f.left (ovw f) (RingHom.id R) (f ≫ g).left (ovw (f ≫ g)) (Over.comp_left _ _ _ f g)
    (fun _ ↦ rfl)).1 a |>.symm

theorem pO1_id {R : Type} [CommRing R] (A : Over (Sp R)) (a : HO1 A.hom) : pO1 (𝟙 A) a = a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.2 R A).1 a

theorem eq_zero_of_base {R : Type} [CommRing R] (a : HO1 (𝟙_ (Over (Sp R))).hom) : a = 0 := by
  haveI := ((GlobalTheory.AbCoh.Vanish.main).1 R (𝟙_ (Over (Sp R))).left (𝟙_ (Over (Sp R))).hom
    (inferInstanceAs (IsAffine (Sp R)))).1
  exact Subsingleton.elim _ _

theorem axes_defect {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (x : HO1 A.hom) :
    pO1 (lift (𝟙 A) (1 : A ⟶ A)) (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) = 0 ∧
    pO1 (lift (1 : A ⟶ A) (𝟙 A)) (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) = 0 := by
  have h1 : ∀ a : HO1 A.hom, pO1 (1 : A ⟶ A) a = 0 := fun a ↦ by
    rw [Hom.one_def, pO1_comp, eq_zero_of_base (pO1 η[A] a), map_zero]
  refine ⟨?_, ?_⟩
  · rw [map_sub, map_sub, ← pO1_comp, ← pO1_comp, ← pO1_comp, lift_fst, lift_snd, ← Hom.mul_def,
      _root_.mul_one, pO1_id, h1, sub_self, sub_zero]
  · rw [map_sub, map_sub, ← pO1_comp, ← pO1_comp, ← pO1_comp, lift_fst, lift_snd, ← Hom.mul_def,
      _root_.one_mul, pO1_id, h1, sub_zero, sub_self]

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A := by
  intro R _ _ t R' _ σ' hsurj hker ht hmt hfield hR' A _ g hab hsm
  letI : Algebra R R' := σ'.toAlgebra
  have hkF : IsField (R ⧸ IsLocalRing.maximalIdeal R) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
  have hSE : SmallExt t (algebraMap R R') (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) := by
    refine ⟨hsurj, hker, Ideal.Quotient.mk_surjective, fun a ↦ ?_⟩
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨hmt a, fun h ↦ ?_⟩
    by_contra hna
    exact ht ((IsLocalRing.notMem_maximalIdeal.mp hna).mul_right_eq_zero.mp h)
  haveI := hsm
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  haveI : Flat A.hom := inferInstance
  have hfl2 : Flat (A ⊗ A).hom := by rw [Over.tensorObj_hom]; infer_instance
  obtain ⟨B', _, pr, pr', hab', hsm', hpr, hpr', hμ', hf', hs', he1', he2'⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R R' A g hab hsm
  obtain ⟨B₀, _, pr0, pr0', hab0, hsm0, hpr0, hpr0', -, -, -, he10, he20⟩ :=
    GlobalTheory.T.exists_abelianScheme_baseChange_and_square R (R ⧸ IsLocalRing.maximalIdeal R) A g hab hsm
  intro x
  have key : pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x = 0 := by
    set y := pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x with hy
    have hnat := GlobalTheory.AbCoh.pull_over_baseChange_comm R R' (algebraMap R R') A (A ⊗ A) B' (B' ⊗ B')
    have ya : pullHO1 hpr'.w y = 0 := by
      have hP := hR' B' g hab' hsm' (pullHO1 hpr.w x)
      rw [hy, map_sub, map_sub, (hnat μ[A] μ[B'] pr pr' hpr.w hpr'.w hμ').1,
        (hnat (fst A A) (fst B' B') pr pr' hpr.w hpr'.w hf').1,
        (hnat (snd A A) (snd B' B') pr pr' hpr.w hpr'.w hs').1, hP]
      abel
    obtain ⟨u, hu⟩ := GlobalTheory.T.eq_smul_residueFibre_class_of_pullback_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
      (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
      (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' hSE hfl2 y ya
    have hH0 := (GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hab) R' B'.left B'.hom pr hpr
    have hax := axes_defect A x
    have hu1 : pO1 (lift (𝟙 B₀) (1 : B₀ ⟶ B₀)) u = 0 :=
      GlobalTheory.T.residueFibre_class_eq_zero_of_smul_pullback_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
        (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
        (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' A.left B'.left B₀.left A.hom B'.hom B₀.hom pr pr0 hpr hpr0
        (lift (𝟙 A) (1 : A ⟶ A)).left (lift (𝟙 B') (1 : B' ⟶ B')).left (lift (𝟙 B₀) (1 : B₀ ⟶ B₀)).left
        (ovw _) (ovw _) (ovw _) he1' he10 hSE hfl2 inferInstance hH0 u y hu hax.1
    have hu2 : pO1 (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)) u = 0 :=
      GlobalTheory.T.residueFibre_class_eq_zero_of_smul_pullback_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
        (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
        (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' A.left B'.left B₀.left A.hom B'.hom B₀.hom pr pr0 hpr hpr0
        (lift (1 : A ⟶ A) (𝟙 A)).left (lift (1 : B' ⟶ B') (𝟙 B')).left (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left
        (ovw _) (ovw _) (ovw _) he2' he20 hSE hfl2 inferInstance hH0 u y hu hax.2
    have hu0 : u = 0 := (hfield _ hkF B₀ g hab0 hsm0).1 u hu1 hu2
    subst hu0
    exact GlobalTheory.T.smallExtension_element_mul_zeroClass_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
      (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
      (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' hSE hfl2 y hu
  rw [sub_sub, sub_eq_zero] at key
  exact key

end GlobalTheory.AbCoh.StepPrim
