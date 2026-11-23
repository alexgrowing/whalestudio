import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasRatioOfHasDRGalois
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRatio_of_hasDR_galois : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → IsGalois ℚ E → ∀ (Z : Mdl Y i₀), HasDR Z → p ∣ Z.i.l.A → ∀ st (x : Letter Dw), letterOf Dw st = some x → HasRatio Z st := by
  first | exact @GlobalTheory.HTLine.Ratio.hasRatio | exact GlobalTheory.HTLine.Ratio.hasRatio | (intros; apply GlobalTheory.HTLine.Ratio.hasRatio <;> assumption)
