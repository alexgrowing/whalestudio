import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionSectionLiftTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointRefinementsCompareUnifStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TwistSec

theorem exists_sec_compare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 ∧ ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ ∀ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D₂.toPre D'.toPre) → Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D'.toPre) := by
  intro R _ _ _ hR D₀ D A G _ _ hG U hS
  obtain ⟨g, h2, hc⟩ := GlobalTheory.T.exists_orderTwo_point_refinements_compare_unif R hR D₀ D A G hG U hS
  obtain ⟨a, ha, hl⟩ := GlobalTheory.T.exists_twoTorsion_section_lift_torusExtension R hR D A G hG U g h2
  refine ⟨a, ha, fun A₂ D₂ U₂ hL => ?_⟩
  obtain ⟨R', i1, i2, i3, ρ, D₁, D₂', hf, hloc, h0, h2', hid⟩ := hc a ha hl A₂ D₂ U₂ hL
  refine ⟨R', i1, i2, i3, ρ, D₁, hf, hloc, h0, fun D' hD' => ?_⟩
  have h3 := isPullDeg_unique_any R R' ρ D₂.toPre D₂'.toPre D'.toPre h2' hD'
  have h4 := nonempty_isPullDeg_comp_of_injective R' R' R' (RingHom.id R') (RingHom.id R') D₁.toPre D₂'.toPre
    D'.toPre Function.injective_id hid h3
  simpa using h4

end GlobalTheory.TwistSec
