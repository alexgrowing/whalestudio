import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingLocalizationOfComapEqBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffinePreimageLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DivStart

theorem exists_locus_over_dense_open : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ (U : (Sp R).Opens) (c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme), (U : Set (Sp R)).Nonempty ∧ IsLocus c ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V) := by
  intro R _ _ _ _ A _ hA V hV hsurj
  have := hA.smooth
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsLocallyNoetherian (Sp R) := inferInstance
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : A.left.IsSeparated := ⟨by rw [← terminal.comp_from A.hom]; infer_instance⟩
  let s₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  obtain ⟨x₀, hx₀, -⟩ := hsurj s₀
  obtain ⟨W₀, hVW, hufd, c₀, hc₀⟩ := GlobalTheory.FactorialLocus.exists_isLocus A.left V hV ⟨x₀, hx₀⟩
  have hfib : ∀ x, A.hom x = s₀ → x ∈ W₀ := fun x hx =>
    hufd x (GlobalTheory.GenericFibreFactorial.ufd_stalk_of_generic R A.left A.hom x (by rw [hx]))
  obtain ⟨U, -, hsU, hUW⟩ := GlobalTheory.Tube.exists_affine_preimage_le A.left (Sp R) A.hom s₀ W₀ hfib
  have hle : A.hom ⁻¹ᵁ U ⊔ V ≤ W₀ := sup_le hUW hVW
  refine ⟨U, GlobalTheory.CechPic.pull (A.left.homOfLE hle) c₀, ⟨s₀, hsU⟩, ?_⟩
  have h := GlobalTheory.LocusPull.isLocus_pull (A.left.homOfLE hle) hc₀
  convert h using 1
  ext x
  change (A.hom ⁻¹ᵁ U ⊔ V).ι x ∈ V ↔ W₀.ι (A.left.homOfLE hle x) ∈ V
  rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]

end GlobalTheory.DivStart
