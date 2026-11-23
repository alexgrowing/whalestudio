import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedGeneratorIsGenerator
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_generator_is_generator : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), (∀ x y : X, ∃ u, RatioProp h x y u) → (sigGen h s).IsGen := by
  first | exact @GlobalTheory.UnitGlue.sigGen_isGen_of_ratio | exact GlobalTheory.UnitGlue.sigGen_isGen_of_ratio | (intros; apply GlobalTheory.UnitGlue.sigGen_isGen_of_ratio <;> assumption)
