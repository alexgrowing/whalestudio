import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyAbelianVarietyAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyResidueFieldFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecialFibreCohomologyLiftArtinianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianSStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitInjectiveOfForallPrimeBaseChangeFieldInject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1Vanish

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.AxesSq

theorem surj_of_comp {R R' : Type} [CommRing R] [CommRing R'] {X X' X₀ : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R}
    {s₀ : X₀ ⟶ Sp R'} {σ : R →+* R'} (e : X ⟶ X') (ψ : X₀ ⟶ X)
    (he : e ≫ s' = s ≫ spMap (RingHom.id R)) (hψ : ψ ≫ s = s₀ ≫ spMap σ) (hc : (ψ ≫ e) ≫ s' = s₀ ≫ spMap σ) :
    (Function.Surjective (pullHO1 hc) → Function.Surjective (pullHO1 hψ)) ∧
    (Function.Surjective (pullHO2 hc) → Function.Surjective (pullHO2 hψ)) := by
  have H := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R X' X s' s (RingHom.id R) e he R' X₀ s₀ σ ψ hψ σ (ψ ≫ e) hc rfl (fun _ ↦ rfl))
  refine ⟨fun h y ↦ ?_, fun h y ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := h y
    exact ⟨pullHO1 he a, H.1 a⟩
  · obtain ⟨a, rfl⟩ := h y
    exact ⟨pullHO2 he a, H.2.1 a⟩

theorem fp_bc1 (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom)) ∧ StructureSheafH1BaseChange A.hom := by
  haveI : Smooth A.hom := hA.smooth
  haveI : IsProper A.hom := hA.proper
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.structure_cohomology_residue_field_fibre R A.left A.hom inferInstance inferInstance (GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hA)
    (by
      intro R' _ _ _ _ k _ _ α hα X' s' φ X₀ s₀ ψ hφ w
      obtain ⟨B, _, pr, -, hB, hBg, hpb, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R R' A g hA hg
      let e : B.left ≅ X' := IsPullback.isoIsPullback _ _ hpb hφ
      have he2 : e.hom ≫ s' = B.hom := IsPullback.isoIsPullback_hom_snd A.left (Sp R') hpb hφ
      have he : e.inv ≫ B.hom = s' ≫ spMap (RingHom.id R') := by
        rw [← he2, Iso.inv_hom_id_assoc]
        first | (rw [spMap_id, Category.comp_id]) | (simp [spMap, CommRingCat.ofHom_id]) | (rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])
      have w' : IsPullback (ψ ≫ e.inv) s₀ B.hom (spMap (α : R' →+* k)) := by
        refine IsPullback.of_iso w (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [← he2]
      obtain ⟨s1, s2⟩ := GlobalTheory.T.abelianSchemeSpecialFibre_cohomology_lift_artinian R' B g hB hBg k α hα X₀ s₀ (ψ ≫ e.inv) w'
      have hc := surj_of_comp (s := s') (s' := B.hom) e.inv ψ he w.w w'.w
      exact ⟨hc.1 s1, hc.2 s2⟩)
  exact ⟨h1, h3⟩

theorem pull1_congr {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
    {σ : R →+* R'} {φ₁ φ₂ : X' ⟶ X} (hφ : φ₁ = φ₂) (h₁ : φ₁ ≫ s = s' ≫ spMap σ) (h₂ : φ₂ ≫ s = s' ≫ spMap σ)
    (c : HO1 s) : pullHO1 h₁ c = pullHO1 h₂ c := by
  subst hφ; rfl

def axesMap {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] :
    HO1 (A ⊗ A).hom →ₗ[R] HO1 A.hom × HO1 A.hom :=
  LinearMap.prod (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))) (pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)))

theorem pO1_bc {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {A Y : Over (Sp R)} {B Z : Over (Sp K)}
    (f : Y ⟶ A) (f' : Z ⟶ B) (pr : Z.left ⟶ Y.left) (pr' : B.left ⟶ A.left)
    (hpb : pr ≫ Y.hom = Z.hom ≫ spMap (algebraMap R K)) (hpb' : pr' ≫ A.hom = B.hom ≫ spMap (algebraMap R K))
    (hc : f'.left ≫ pr' = pr ≫ f.left) (c : HO1 A.hom) :
    pO1 f' (pullHO1 hpb' c) = pullHO1 hpb (pO1 f c) := by
  have h1 : (f'.left ≫ pr') ≫ A.hom = Z.hom ≫ spMap (algebraMap R K) := by
    rw [Category.assoc, hpb', ← Category.assoc, Over.w]
  have h2 : (pr ≫ f.left) ≫ A.hom = Z.hom ≫ spMap (algebraMap R K) := by rw [← hc]; exact h1
  have E1 := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R K A.left B.left A.hom B.hom (algebraMap R K) pr' hpb' K Z.left Z.hom (RingHom.id K)
    f'.left (ovw f') (algebraMap R K) (f'.left ≫ pr') h1 rfl (fun _ ↦ rfl)).1 c
  have E2 := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R A.left Y.left A.hom Y.hom (RingHom.id R) f.left (ovw f) K Z.left Z.hom (algebraMap R K)
    pr hpb (algebraMap R K) (pr ≫ f.left) h2 rfl (fun _ ↦ rfl)).1 c
  unfold pO1
  rw [E1, E2]
  exact pull1_congr hc h1 h2 c

theorem axesMap_baseChange_injective (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (K : Type) [Field K] [IsAlgClosed K] [Algebra R K] :
    Function.Injective ((axesMap A).baseChange K) := by
  obtain ⟨hsq, hsqg⟩ := (GlobalTheory.Obs.sq_abelian_and_affine_H1 R).1 A g hA hg
  obtain ⟨B, _, pr, pr', hB, hBg, hpb, hpb', -, -, -, h1, h2⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R K A g hA hg
  obtain ⟨eS, heS⟩ := (fp_bc1 R (A ⊗ A) (g + g) hsq hsqg).2 K _ _ pr' hpb'
  obtain ⟨eA, heA⟩ := (fp_bc1 R A g hA hg).2 K _ _ pr hpb
  have key : ∀ (f : A ⟶ A ⊗ A) (f' : B ⟶ B ⊗ B), f'.left ≫ pr' = pr ≫ f.left →
      ∀ z, pO1 f' (eS z) = eA ((pO1 f).baseChange K z) := by
    intro f f' hc z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      have : a ⊗ₜ[R] c = a • ((1 : K) ⊗ₜ[R] c) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [this, map_smul, map_smul, map_smul, LinearMap.baseChange_tmul, map_smul, heS, heA]
      congr 1
      exact pO1_bc f f' pr pr' hpb.w hpb'.w hc c
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨-, -, -, -, hax⟩ := GlobalTheory.T.structureSheafCohomology_abelianVariety_algClosed K B g hB hBg
  intro z z' hzz
  rw [← sub_eq_zero] at hzz ⊢
  rw [← map_sub] at hzz
  generalize z - z' = w at hzz ⊢
  have hfst : (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))).baseChange K w = 0 := by
    have := congrArg ((LinearMap.fst R (HO1 A.hom) (HO1 A.hom)).baseChange K) hzz
    rwa [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp] at this
  have hsnd : (pO1 (lift (toUnit A ≫ η[A]) (𝟙 A))).baseChange K w = 0 := by
    have := congrArg ((LinearMap.snd R (HO1 A.hom) (HO1 A.hom)).baseChange K) hzz
    rwa [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp] at this
  have e0 : eS w = 0 := by
    apply hax
    · have k1 := key (lift (𝟙 A) (toUnit A ≫ η[A])) (lift (𝟙 B) (toUnit B ≫ η[B])) h1 w
      rw [k1, hfst, map_zero]
    · have k2 := key (lift (toUnit A ≫ η[A]) (𝟙 A)) (lift (toUnit B ≫ η[B]) (𝟙 B)) h2 w
      rw [k2, hsnd, map_zero]
  simpa using congrArg eS.symm e0

theorem axesO1_of_isAbelianScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → AxesVanishingStructureSheafDegOne A := by
  intro R _ _ A _ g hA hg
  obtain ⟨hsq, hsqg⟩ := (GlobalTheory.Obs.sq_abelian_and_affine_H1 R).1 A g hA hg
  obtain ⟨⟨hS1, hS2⟩, -⟩ := fp_bc1 R (A ⊗ A) (g + g) hsq hsqg
  obtain ⟨⟨hA1, hA2⟩, -⟩ := fp_bc1 R A g hA hg
  let e1 : ULift.{1} (HO1 (A ⊗ A).hom) ≃ₗ[R] HO1 (A ⊗ A).hom := ULift.moduleEquiv
  let e2 : ULift.{1} (HO1 A.hom × HO1 A.hom) ≃ₗ[R] HO1 A.hom × HO1 A.hom := ULift.moduleEquiv
  let f : ULift.{1} (HO1 (A ⊗ A).hom) →ₗ[R] ULift.{1} (HO1 A.hom × HO1 A.hom) :=
    e2.symm.toLinearMap ∘ₗ axesMap A ∘ₗ e1.toLinearMap
  haveI : Module.Finite R (ULift.{1} (HO1 (A ⊗ A).hom)) := Module.Finite.equiv e1.symm
  haveI : Module.Projective R (ULift.{1} (HO1 (A ⊗ A).hom)) := Module.Projective.of_equiv e1.symm
  haveI : Module.Finite R (ULift.{1} (HO1 A.hom × HO1 A.hom)) := Module.Finite.equiv e2.symm
  haveI : Module.Projective R (ULift.{1} (HO1 A.hom × HO1 A.hom)) := Module.Projective.of_equiv e2.symm
  obtain ⟨r, hr⟩ := GlobalTheory.split_injective_of_forall_prime_baseChange_field_injective R _ _ f (by
    intro P
    refine ⟨AlgebraicClosure P.asIdeal.ResidueField, inferInstance, inferInstance, ?_, ?_⟩
    · have hk : RingHom.ker (algebraMap P.asIdeal.ResidueField (AlgebraicClosure P.asIdeal.ResidueField)) = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap P.asIdeal.ResidueField _).injective
      rw [IsScalarTower.algebraMap_eq R P.asIdeal.ResidueField (AlgebraicClosure P.asIdeal.ResidueField),
        ← RingHom.comap_ker, hk]
      exact Ideal.ker_algebraMap_residueField _
    · have hi := axesMap_baseChange_injective R A g hA hg (AlgebraicClosure P.asIdeal.ResidueField)
      simp only [f, LinearMap.baseChange_comp]
      exact (e2.symm.baseChange R _ _ _).injective.comp (hi.comp (e1.baseChange R _ _ _).injective))
  have hf : Function.Injective f := fun x y hxy ↦ by
    have := congrArg r hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hr, LinearMap.id_apply, LinearMap.id_apply] at this
  intro y hy1 hy2
  have h0 : f (e1.symm y) = f 0 := by
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_zero]
    simp [axesMap, hy1, hy2]
  simpa using congrArg e1 (hf h0)

end GlobalTheory.AbCoh.AxesSq
