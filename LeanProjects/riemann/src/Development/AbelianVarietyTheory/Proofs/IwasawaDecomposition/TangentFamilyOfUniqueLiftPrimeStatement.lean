import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentFamilyOfUniqueLiftPrime
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_family_of_unique_lift_prime : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : ℕ) (C : Formalism.MainNotions.DIV.Cons.SCF p) (b : Bool) (xO : Sp ↥(intO ↥C.S) ⟶ X), p.Prime → (∀ y : Sp ↥(intO ↥C.S) ⟶ X, spMap (intO ↥C.S).subtype ≫ y = spMap (intO ↥C.S).subtype ≫ xO → y = xO) → ∀ (m : ℕ) (u : Fin m → (Sp (DualNumber ↥C.S) ⟶ t.G.left)), (∀ i, IsTanAtG t (spMap (intO ↥C.S).subtype ≫ xO) (u i)) → (∀ cf cf' w, IsCombAtG t (spMap (intO ↥C.S).subtype ≫ xO) u cf w → IsCombAtG t (spMap (intO ↥C.S).subtype ≫ xO) u cf' w → cf = cf') → ∀ i, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ↥C.S).subtype ≫ xO) (lat t p (spMap (intO ↥C.S).subtype ≫ xO) b) u i := by
  first | exact @GlobalTheory.GrNormPos.grNorm_pos | exact GlobalTheory.GrNormPos.grNorm_pos | (intros; apply GlobalTheory.GrNormPos.grNorm_pos <;> assumption)
