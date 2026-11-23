import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DividesOfNormBoundedPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divides_of_norm_bounded_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (U : Z.X.Opens), IsAffineOpen U → ∀ a b : Γ(Z.X, U), (p : Γ(Z.X, U)) ∈ (Ideal.span {b}).radical → (∀ y : Z.Pt, ⊤ ≤ y.z ⁻¹ᵁ U → ‖valF y.gen U a‖ ≤ ‖valF y.gen U b‖) → b ∣ a := by
  first | exact @GlobalTheory.HTLine.Dvd.dvd_of_forall_pt | exact GlobalTheory.HTLine.Dvd.dvd_of_forall_pt | (intros; apply GlobalTheory.HTLine.Dvd.dvd_of_forall_pt <;> assumption)
