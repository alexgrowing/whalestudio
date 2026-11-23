import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityAndPValuation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roots_of_unity_and_p_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → (∀ N : ℕ, N ∣ l.A → ∃ ζ : ↥(c.V W), IsPrimitiveRoot ζ N) ∧ (IsGalois ℚ E → ∃ a : ↥(c.V W), (p : ↥(c.V W)) ∈ (Ideal.span {a}).radical ∧ ∀ (C : SCF p) (φ : ↥(c.V W) →+* ↥(intO ↥C.S)), Real.log ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ = -(vDiff E p * Real.log p)) := by
  first | exact @GlobalTheory.HTConst.const_main | exact GlobalTheory.HTConst.const_main | (intros; apply GlobalTheory.HTConst.const_main <;> assumption)
