import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizationSectionExpansion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformization_section_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (q : ℕ), 1 ≤ q →
    ∀ (Φ : Fam D.toPre (FractionRing R) q) (f : ∀ α, D.toPre.SecB q α),
      (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) →
      ∃ σ : H0 U.LG.L q, ∀ e : ℕ, U.ExpandsAt e q σ f := by
  first | exact @GlobalTheory.IntegralLift.main | exact GlobalTheory.IntegralLift.main | (intros; apply GlobalTheory.IntegralLift.main <;> assumption)
