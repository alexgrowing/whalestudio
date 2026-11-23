import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsRingHomValuationRingOfEmbOK
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_valuationRing_of_embOK : ∀ (T : CDVR) (C : Type) [Field C] [CharZero C] (V : VF C) (ι' : T.Fr →+* C), EmbOK T V ι' → ∃ j : T.V →+* V.RR, (∀ x, (j x : C) = ι' (algebraMap T.V T.Fr x)) ∧ ∀ x ∈ maximalIdeal T.V, V.MM (j x : C) := by
  first | exact @GlobalTheory.embOK_exists_ringHom | exact GlobalTheory.embOK_exists_ringHom | (intros; apply GlobalTheory.embOK_exists_ringHom <;> assumption)
