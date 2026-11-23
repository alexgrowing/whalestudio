import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegDataIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumPull

theorem specOf_genericPoint {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) :
    (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  show Ideal.comap ρ ⊥ = ⊥
  exact Ideal.comap_bot_of_injective ρ hρ

theorem exists_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → IsLocalHom ρ → ∀ D : DegData R (maximalIdeal R), ∃ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D.toPre D'.toPre) := by
  intro R R' _ _ _ _ _ _ ρ hρ hloc D
  obtain ⟨L, -⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
  obtain ⟨W, hW, hψ⟩ := GlobalTheory.PsiSpread.exists_psiOn D.toPre D.tau_bimult
  have hη : (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W := by
    rw [specOf_genericPoint ρ hρ]; exact hW
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal R' :=
    ((IsLocalRing.local_hom_TFAE ρ).out 0 2).1 hloc
  obtain ⟨D', hD, -, -⟩ := GlobalTheory.exists_degData_isPullDeg L.polBaseChange L.globalFns R R' (maximalIdeal R)
    (maximalIdeal R') ρ hI D W hψ hη
  exact ⟨D', ⟨hD⟩⟩

end GlobalTheory.MumPull
