import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.LogbNormUniformizerNormalisation
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logb_norm_uniformizer_normalisation : ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (C : SCF (Formalism.MainNotions.WeightAlgebra.resCh la)) (f : T.V →+* ↥C.S), (∀ a, ‖f a‖ ≤ 1) → -Real.logb (Formalism.MainNotions.WeightAlgebra.resCh la) ‖f ϖ‖ * ((e : ℝ) * Formalism.BasicNotions.eWL K la) = 1 ∧ 0 < Formalism.BasicNotions.eWL K la := by
  first | exact @GlobalTheory.EtaVal.UnitNorm.logb_norm_uniformiser | exact GlobalTheory.EtaVal.UnitNorm.logb_norm_uniformiser | (intros; apply GlobalTheory.EtaVal.UnitNorm.logb_norm_uniformiser <;> assumption)
