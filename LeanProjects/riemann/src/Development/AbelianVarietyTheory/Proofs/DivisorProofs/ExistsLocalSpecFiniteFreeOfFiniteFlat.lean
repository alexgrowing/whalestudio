import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCover
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

namespace GlobalTheory.FiniteFlatLocal

theorem exists_finFree_local : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ s : S, ∃ (W : S.Opens) (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Free A B) (_ : Module.Finite A B) (eW : W.toScheme ≅ Spec (CommRingCat.of A)) (eZ : (z ⁻¹ᵁ W).toScheme ≅ Spec (CommRingCat.of B)), s ∈ W ∧ eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = (z ∣_ W) ≫ eW.hom := by
  intro S Z z h1 h2 h3 s
  obtain ⟨V, hV, hsV, -, hF⟩ := GlobalTheory.FiniteAmpleFP.exists_finFree_app_fp z (x := s) (U := ⊤) trivial
  have hZ : IsAffineOpen (z ⁻¹ᵁ V) := hV.preimage z
  letI : Algebra Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := (z.app V).hom.toAlgebra
  have hfin : Module.Finite Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := hF.1
  have hfree : Module.Free Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := hF.2
  refine ⟨V, Γ(S, V), Γ(Z, z ⁻¹ᵁ V), inferInstance, inferInstance, inferInstance, hfree, hfin,
    hV.isoSpec, hZ.isoSpec, hsV, ?_⟩
  have e := IsAffineOpen.SpecMap_appLE_fromSpec z hV hZ le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at e
  rw [← cancel_mono (hV.isoSpec.inv ≫ V.ι)]
  rw [IsAffineOpen.isoSpec_inv_ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    morphismRestrict_ι, ← IsAffineOpen.isoSpec_hom_fromSpec hZ, Category.assoc, ← e]
  rfl

end GlobalTheory.FiniteFlatLocal
