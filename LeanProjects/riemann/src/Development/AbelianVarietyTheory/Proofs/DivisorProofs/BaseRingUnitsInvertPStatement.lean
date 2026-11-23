import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseRingUnitsInvertP
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_ring_units_invert_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l' : Level H) (c' : Coeff l') (W : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (A : Type) [CommRing A] (β : c'.V W →+* A), IsUnit (p : A) → ∀ a : c'.V W, a ≠ 0 → IsUnit (β a) := by
  first | exact @GlobalTheory.CoeffUnit.isUnit_of_ne_zero | exact GlobalTheory.CoeffUnit.isUnit_of_ne_zero | (intros; apply GlobalTheory.CoeffUnit.isUnit_of_ne_zero <;> assumption)
