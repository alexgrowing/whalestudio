import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoSectionTranslateRefinementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalSymmetricBundleTranslateOrderTwStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationGenericFibreTwoTorsioStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumTwist

theorem exists_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ (a : 𝟙_ (Over (Sp R)) ⟶ G) (P : GlobalTheory.UU.CP G) (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), a ^ 2 = 1 ∧ LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P ∧ IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) ∧ ∀ (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), U₂.LG = P.L → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ ∀ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D₂.toPre D'.toPre) → Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D'.toPre) := by
  intro R _ _ _ hR D₀ D A G _ _ hG U hS
  obtain ⟨a, ha, hcmp⟩ := GlobalTheory.T.exists_orderTwo_section_translate_refinement R hR D₀ D A G hG U hS
  obtain ⟨P, hP, hE⟩ := GlobalTheory.T.exists_evenCubicalSymmetricBundle_translate_orderTwo R hR D A G hG U a ha
  obtain ⟨A₂, gen₂, hm, hl⟩ := GlobalTheory.T.exists_principal_polarisation_genericFibre_twoTorsion_translate R hR D A G hG U a ha P hP
  refine ⟨a, P, A₂, gen₂, ha, hP, hE, hm, hl, fun D₂ U₂ hU => ?_⟩
  exact hcmp A₂ D₂ U₂ (by rw [hU]; exact hP)

end GlobalTheory.MumTwist
