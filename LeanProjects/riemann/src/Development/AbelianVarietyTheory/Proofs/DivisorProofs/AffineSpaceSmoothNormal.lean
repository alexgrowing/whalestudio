import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem smooth_affineSpace_over_of_isAffine (S : Scheme.{0}) [IsAffine S] (ι : Type) [Finite ι] :
    Smooth (𝔸(ι; S) ↘ S) := by
  have e : (𝔸(ι; S) ↘ S) = (AffineSpace.isoOfIsAffine ι S).hom ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ S.isoSpec.inv := by
    rw [← AffineSpace.isoOfIsAffine_inv_over (n := ι) (S := S), Iso.hom_inv_id_assoc]
  rw [e]
  haveI : Algebra.Smooth Γ(S, ⊤) (MvPolynomial ι Γ(S, ⊤)) := ⟨inferInstance, inferInstance⟩
  have : Smooth (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := Γ(S, ⊤)) (σ := ι)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  infer_instance

theorem isIntegrallyClosed_stalk_spec_field (K : Type) [Field K] (x : Spec (.of K)) :
    IsIntegrallyClosed ((Spec (.of K)).presheaf.stalk x) := by
  have hU := isAffineOpen_top (Spec (.of K))
  letI := (Spec (.of K)).presheaf.algebra_section_stalk (⟨x, trivial⟩ : (⊤ : (Spec (.of K)).Opens))
  have h1 := hU.isLocalization_stalk ⟨x, trivial⟩
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  exact (isDomain_and_isIntegrallyClosed_atPrime_of_isDomain (hU.primeIdealOf ⟨x, trivial⟩).asIdeal
    ((Spec (.of K)).presheaf.stalk x)).2

theorem affineSpace_over_integral_affine_open_smooth_integral_normal :
    ∀ (X : Scheme.{0}) (K : Type) [Field K] (s : X ⟶ Spec (.of K)), Smooth s →
    ∀ (V : X.Opens), IsAffineOpen V → IsIntegral V.toScheme → ∀ (ι : Type) [Finite ι],
    Smooth ((𝔸(ι; V.toScheme) ↘ V.toScheme) ≫ V.ι) ∧
    LocallyOfFiniteType ((𝔸(ι; V.toScheme) ↘ V.toScheme) ≫ V.ι) ∧
    IsIntegral 𝔸(ι; V.toScheme) ∧
    ∀ t : 𝔸(ι; V.toScheme), IsIntegrallyClosed (𝔸(ι; V.toScheme).presheaf.stalk t) := by
  intro X K _ s hs V hV hint ι _
  have : IsAffine V.toScheme := hV
  have : Smooth (𝔸(ι; V.toScheme) ↘ V.toScheme) := smooth_affineSpace_over_of_isAffine _ ι
  have h1 : Smooth ((𝔸(ι; V.toScheme) ↘ V.toScheme) ≫ V.ι) := inferInstance
  refine ⟨h1, inferInstance, inferInstance, fun t ↦ ?_⟩
  have : Smooth (((𝔸(ι; V.toScheme) ↘ V.toScheme) ≫ V.ι) ≫ s) := inferInstance
  exact (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth
    (((𝔸(ι; V.toScheme) ↘ V.toScheme) ≫ V.ι) ≫ s)
    (fun y ↦ ⟨inferInstance, isIntegrallyClosed_stalk_spec_field K y⟩) t).2

end GlobalTheory
