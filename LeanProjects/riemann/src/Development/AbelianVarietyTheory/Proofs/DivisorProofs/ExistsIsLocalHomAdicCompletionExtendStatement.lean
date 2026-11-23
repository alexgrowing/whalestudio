import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalHomAdicCompletionExtend
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_apply : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (V : Type) [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (ψ : O →+* V), IsLocalHom ψ → ∃ ev₀ : AdicCompletion (maximalIdeal O) O →+* V, IsLocalHom ev₀ ∧ ∀ a, ev₀ (algebraMap O _ a) = ψ a := by
  first | exact @GlobalTheory.exists_isLocalHom_adicCompletion_extend | exact GlobalTheory.exists_isLocalHom_adicCompletion_extend | (intros; apply GlobalTheory.exists_isLocalHom_adicCompletion_extend <;> assumption)
