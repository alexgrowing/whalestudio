import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndUOfOLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem GlobalTheory.USep.conjAct_endU_chars : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (a : 𝓞 E), ∃ En : GlobalTheory.UT.EndU P.U.toUnifPre, En.aA = (letI := H.starRing; P.oA.act (H.bar a)) ∧ ∀ x, En.h x = a • x := by
  intro E _ _ _ H V _ _ _ hV t P a
  letI := H.starRing
  haveI : CharZero V := hV.2.2.2
  obtain ⟨En, -, hA, -, hh, -⟩ := GlobalTheory.Mum.EFix.endU_of_oLinear GlobalTheory.firstFiveLaws V (maximalIdeal V)
    ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩ P.D P.A t.G t.semi P.U (𝓞 E) P.oD P.oA t.act.toRingAct P.lin (H.bar a)
  refine ⟨En, hA, fun x => ?_⟩
  rw [hh]
  exact congrArg (· • x) (star_star a)
