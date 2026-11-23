import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PresentationTangentCombination
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.presentation_tangent_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : ℕ) (b : Bool) (g M : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin (M + 1) → Fin g → R), p.Prime → GlobalTheory.LineNorm.IsTanBasis t x e → Pres t x p b e h → ∀ (m : ℕ) (w : Fin m → (Sp (DualNumber R) ⟶ t.G.left)), (∀ j, IsTanAtG t x (w j)) → (∀ (k : Type) [Field k] (ψ : R →+* k), (p : k) ≠ 0 → Pull.Ind t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ w j)) → ∀ i : Fin m, ∃ (a a' : ℕ) (A : Fin a → R) (B : Fin a' → R), (p : R) ∈ (Ideal.span (Set.range A)).radical ∧ (p : R) ∈ (Ideal.span (Set.range B)).radical ∧ ∀ (C : SCF p) (φ : R →+* ↥(intO ↥C.S)), GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (lat t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) b) (fun j => spMap (dualMap ((intO ↥C.S).subtype.comp φ)) ≫ w j) i * ‖fun j => ((φ (B j) : ↥(intO ↥C.S)) : ↥C.S)‖ = ‖fun j => ((φ (A j) : ↥(intO ↥C.S)) : ↥C.S)‖ := by
  first | exact @GlobalTheory.HTLine.GrMinor.grNorm_eq_ratio | exact GlobalTheory.HTLine.GrMinor.grNorm_eq_ratio | (intros; apply GlobalTheory.HTLine.GrMinor.grNorm_eq_ratio <;> assumption)
