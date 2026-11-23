import Mathlib
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem baseChange_field_fibre_isPreirreducible :
    ∀ (K K' : Type) [Field K] [Field K'] [Algebra K K'] (X X' : AlgebraicGeometry.Scheme.{0}) (g : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)) (p : X' ⟶ X) (g' : X' ⟶ AlgebraicGeometry.Spec (CommRingCat.of K')), CategoryTheory.IsPullback p g' g (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K K'))) → ∀ x : X, (letI : Algebra K (X.residueField x) := (AlgebraicGeometry.Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra; IsDomain (TensorProduct K (X.residueField x) K')) → IsPreirreducible ((⇑p) ⁻¹' {x}) := by
  intro K K' _ _ _ X X' g p g' h x hd
  letI : Algebra K (X.residueField x) := (Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra
  have h1 : IsPullback (p.fiberι x) (p.fiberToSpecResidueField x) p (X.fromSpecResidueField x) :=
    IsPullback.of_hasPullback _ _
  have h3 := h1.paste_horiz h.flip
  have hg : X.fromSpecResidueField x ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap K (X.residueField x))) := by
    rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ g)]
    rfl
  rw [hg] at h3
  let e : p.fiber x ≅ Spec (.of (TensorProduct K (X.residueField x) K')) :=
    h3.flip.isoPullback ≪≫ pullbackSpecIso K (X.residueField x) K'
  have : IsIntegral (Spec (.of (TensorProduct K (X.residueField x) K'))) := inferInstance
  have : IsIntegral (p.fiber x) := IsIntegral.of_isIso e.inv
  rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
  exact (PreirreducibleSpace.isPreirreducible_univ).image _ (p.fiberι x).continuous.continuousOn

end GlobalTheory
