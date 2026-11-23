import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizontalLieDeterminantSectionOfConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHorizontalLieDeterminantSection_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) (e : c.F →+* ℂ), SecU Xo c U τ σ → IsFlatAt Xo c U τ σ ((starRingEnd ℂ).comp e) → IsFlatAt Xo c U τ σ e := by
  first | exact @GlobalTheory.isFlatAt_of_conj | exact GlobalTheory.isFlatAt_of_conj | (intros; apply GlobalTheory.isFlatAt_of_conj <;> assumption)
