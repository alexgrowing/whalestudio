import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyWedgeNoPrimitiveH2Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyResidueFieldFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecialFibreCohomologyLiftArtinianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianSStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1VanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullbackStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.NoPrimNoeth

theorem injective_of_algClosure (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Projective R N] (f : M →ₗ[R] N)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], Function.Injective (f.baseChange K)) :
    Function.Injective f := by
  obtain ⟨g, hg⟩ : ∃ g : N →ₗ[R] M, g ∘ₗ f = LinearMap.id := by
    refine GlobalTheory.split_injective_of_forall_lTensor_residueField_injective f fun m hm => ?_
    let k := AlgebraicClosure m.ResidueField
    have hinj := h k
    have e : (AlgebraTensorModule.cancelBaseChange R m.ResidueField m.ResidueField k N) ∘
          ((f.baseChange m.ResidueField).lTensor k) =
        (f.lTensor k) ∘ (AlgebraTensorModule.cancelBaseChange R
          m.ResidueField m.ResidueField k M) := by
      funext x
      exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
        m.ResidueField m.ResidueField (M := k) f) x).symm
    have h1 : Function.Injective ((f.baseChange m.ResidueField).lTensor k) :=
      Function.Injective.of_comp (e ▸ (hinj.comp (LinearEquiv.injective _)))
    haveI : Module.FaithfullyFlat m.ResidueField k :=
      (fun (F L : Type) [Field F] [Field L] [Algebra F L] ↦ (inferInstance : Module.FaithfullyFlat F L)) _ _
    exact (Module.FaithfullyFlat.lTensor_injective_iff_injective m.ResidueField k _).1 h1
  exact Function.LeftInverse.injective (g := g) fun x ↦ LinearMap.congr_fun hg x

theorem abelian_scheme_second_cohomology_finite_projective (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    (Module.Finite R (HO2 A.hom) ∧ Module.Projective R (HO2 A.hom)) ∧ StructureSheafH2BaseChange A.hom := by
  have hsm : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  have H := GlobalTheory.T.structure_cohomology_residue_field_fibre R A.left A.hom hA.proper inferInstance (GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hA) (by
    intro R' _ _ _ _ k _ _ α hα X' s' φ X₀ s₀ ψ hp w
    obtain ⟨_, -, h1, h2⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R' (algebraMap R R') A X' s' φ hp
    exact GlobalTheory.T.abelianSchemeSpecialFibre_cohomology_lift_artinian R' (Over.mk s' : Over (Sp R')) g (h1 hA) (h2 g hg) k (α : R' →+* k) hα X₀ s₀ ψ w)
  exact ⟨H.2.1, H.2.2.2⟩

theorem pull_comm {R K : Type} [CommRing R] [CommRing K] {σ : R →+* K} {A A' : Over (Sp R)} {B B' : Over (Sp K)}
    {pr : B.left ⟶ A.left} {pr' : B'.left ⟶ A'.left} (h : pr ≫ A.hom = B.hom ≫ spMap σ)
    (h' : pr' ≫ A'.hom = B'.hom ≫ spMap σ) (f : A' ⟶ A) (f' : B' ⟶ B) (e : f'.left ≫ pr = pr' ≫ f.left)
    (c : HO2 A.hom) : pullHO2 h' (structureSheafH2Pullback f c) = structureSheafH2Pullback f' (pullHO2 h c) := by
  have h'' : (pr' ≫ f.left) ≫ A.hom = B'.hom ≫ spMap σ := by rw [Category.assoc, Over.w f, h']
  have a1 := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R _ _ A.hom A'.hom (RingHom.id R) f.left (ovw f) K _ B'.hom σ pr' h' σ _ h''
    rfl (fun _ ↦ rfl)).2.1 c
  have a2 := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R K _ _ A.hom B.hom σ pr h K _ B'.hom (RingHom.id K) f'.left (ovw f') σ _ h''
    e.symm (fun _ ↦ rfl)).2.1 c
  exact a1.trans a2.symm

theorem noPrimO2_of_isNoetherianRing : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → NoPrimitiveStructureSheafH2 A := by
  intro R _ _ A _ g hA hg
  obtain ⟨⟨_, _⟩, bc⟩ := abelian_scheme_second_cohomology_finite_projective R A g hA hg
  obtain ⟨hA2, hg2⟩ := (GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg
  obtain ⟨⟨_, _⟩, bc2⟩ := abelian_scheme_second_cohomology_finite_projective R (A ⊗ A) (g + g) hA2 hg2
  let D : HO2 A.hom →ₗ[R] HO2 (A ⊗ A).hom := structureSheafH2Pullback μ[A] - structureSheafH2Pullback (fst A A) - structureSheafH2Pullback (snd A A)
  have hD : Function.Injective D := by
    refine injective_of_algClosure R _ _ D fun K _ _ _ ↦ ?_
    obtain ⟨B, _, pr, pr', hB, hgB, p1, p2, eμ, e1, e2, -, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R K A g hA hg
    obtain ⟨e, he⟩ := bc K _ _ _ p1
    obtain ⟨e', he'⟩ := bc2 K _ _ _ p2
    have hN := (GlobalTheory.T.abelian_variety_wedge_no_primitive_h2 K B g hB hgB).2
    let DB : HO2 B.hom →ₗ[K] HO2 (B ⊗ B).hom := structureSheafH2Pullback μ[B] - structureSheafH2Pullback (fst B B) - structureSheafH2Pullback (snd B B)
    have key : ∀ x, e' (D.baseChange K x) = DB (e x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a c =>
        have : a ⊗ₜ[R] c = a • ((1 : K) ⊗ₜ[R] c) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [this, map_smul, map_smul, map_smul, map_smul, LinearMap.baseChange_tmul, he, he']
        congr 1
        simp only [D, DB, LinearMap.sub_apply, map_sub]
        rw [pull_comm p1.w p2.w _ _ eμ, pull_comm p1.w p2.w _ _ e1, pull_comm p1.w p2.w _ _ e2]
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : DB (e x) = 0 := by rw [← key, hx, map_zero]
    have h1 : e x = 0 := hN _ (by
      simp only [DB, LinearMap.sub_apply] at h0
      rw [sub_sub, sub_eq_zero] at h0
      exact h0)
    exact e.map_eq_zero_iff.1 h1
  intro z hz
  refine (injective_iff_map_eq_zero D).1 hD z ?_
  simp only [D, LinearMap.sub_apply]
  rw [hz]; abel

end GlobalTheory.AbCoh.NoPrimNoeth
