import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.ExistsMetricExtB

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Set MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.TwistTop
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.ArithmeticHeightTower.Read1

open GlobalTheory.Amb GlobalTheory.Published GlobalTheory.Published.Amb

theorem heights_of_form_mix (HF : FormZ) (HM : MixZ) : HeightsZ ∧ HeightsQ := by
  have H := GlobalTheory.T.arithHeightsAndForms_of_intersection_and_inductive (form HF) (mix HM)
  refine ⟨fun m n M _ => ?_, fun n' m n M _ => ?_⟩
  · have := isIntegral_mp ℤ m n
    exact (H ℤ _ _ _ (isArithVar_mpZ m n)).1 M
  · have := (isArithVar_qp n' m n).isIntegral
    exact (H ℤ _ _ _ (isArithVar_qp n' m n)).1 _

theorem bridge3 (HF : FormZ) (HM : MixZ) (HP : ProjQ) : ArFormExists ∧ ArMix ∧ HeightProjection :=
  ⟨form HF, mix HM, proj (heights_of_form_mix HF HM).1 (heights_of_form_mix HF HM).2 HP⟩

end GlobalTheory.ArithmeticHeightTower.Read1
