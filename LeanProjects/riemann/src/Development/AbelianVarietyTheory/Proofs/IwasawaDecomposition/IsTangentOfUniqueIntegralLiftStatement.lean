import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTangentOfUniqueIntegralLift
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTangent_of_unique_integral_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (mu : SABMap t' t f) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (b : Bool) (xO : Sp ↥(intO C) ⟶ X'), (∀ y : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ xO ≫ f → y = xO ≫ f) → ∀ v, IsTanAtG t' (spMap (intO C).subtype ≫ xO) v → (v ∈ lat t' p (spMap (intO C).subtype ≫ xO) b ↔ v ≫ mu.φ ∈ lat t p (spMap (intO C).subtype ≫ xO ≫ f) b) := by
  first | exact @GlobalTheory.ShFam.LatPush.lat_push | exact GlobalTheory.ShFam.LatPush.lat_push | (intros; apply GlobalTheory.ShFam.LatPush.lat_push <;> assumption)
