import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedTwistedFactorValueAtLatticePoint
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedTwistedFactor_value_at_latticePoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (ν mu β₀ β₁ : D.toPre.X), β₁ = β₀ + shift h h' n j ν → ∀ (u₁ : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a ν β₀ β₁) (dε n j))), IsFac D.toPre a h n j ν β₀ β₁ u₁ → ∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val u₁ ((DegPre.zF D.toPre (FractionRing R)).left ≫ (DegPre.trF D.toPre (FractionRing R) mu).left) z J = (val (D.toPre.psi (ν + mu)) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.toPre.psi (h (ν + mu))) (jFK (R := R) (FractionRing R)) z J ^ j * val (D.toPre.tau (ν + mu) β₀) (jFK (R := R) (FractionRing R)) z J * val D.toPre.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j)) * (val (D.toPre.psi mu) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.toPre.psi (h mu)) (jFK (R := R) (FractionRing R)) z J ^ j * val (D.toPre.tau mu β₁) (jFK (R := R) (FractionRing R)) z J * val D.toPre.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j))⁻¹ := by
  first | exact @GlobalTheory.TwFacVal.val_fac_at_point | exact GlobalTheory.TwFacVal.val_fac_at_point | (intros; apply GlobalTheory.TwFacVal.val_fac_at_point <;> assumption)
