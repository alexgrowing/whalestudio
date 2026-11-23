import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateActionUniformisationCharacters
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateAction_uniformisation_characters : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (a : 𝓞 E), ∃ En : GlobalTheory.UT.EndU P.U.toUnifPre, En.aA = (letI := H.starRing; P.oA.act (H.bar a)) ∧ ∀ x, En.h x = a • x := by
  first | exact @GlobalTheory.USep.conjAct_endU_chars | exact GlobalTheory.USep.conjAct_endU_chars | (intros; apply GlobalTheory.USep.conjAct_endU_chars <;> assumption)
