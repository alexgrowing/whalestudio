import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianEndomorphismUniqueOverDegenerationDatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismUniformisedGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniformisationEndomorphismLiesOverAdjointStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem linEnd_adjoint_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → LinEnd U.toUnifPre a' h g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE g g' hg hg'
  obtain ⟨g₁, hg₁, hiso⟩ := GlobalTheory.T.exists_adjoint_endomorphism_uniformised_group R hR D A G hG U g hg.1
  have h₁ : LinEnd U.toUnifPre a' h g₁ := GlobalTheory.T.adjoint_uniformisationEndomorphism_lies_over_adjoint R hR D A G hG U a a' h h' hE g g₁ hg hg₁ hiso
  have hu := GlobalTheory.T.semiAbelian_endomorphism_unique_over_degenerationData R hR.1 D A G hG U a' h
  have heq : g₁ = g' := hu.2 g₁ g' fun e => congrFun (hu.1 _ _ h₁.2 hg'.2) e
  subst heq
  exact hiso

end GlobalTheory.Mum
