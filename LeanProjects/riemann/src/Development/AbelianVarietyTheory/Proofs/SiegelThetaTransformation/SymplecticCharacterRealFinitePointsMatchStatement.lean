import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatch
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticCharacter_real_finite_points_match : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∀ (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (t : D.host.F), symplO S T (ratW T S yᵀ) (ratW T S y'ᵀ) = algebraMap D.host.F (AF D.host.F) t → ∑ k, EF C.X (y k) (y' k) = -Algebra.trace ℚ D.host.F t) ∧ (∀ w w' : WO S T, IsRealPt w → IsRealPt w' → C.ψ (symplOH S T w w') = cexp (π * I * (EFR C.X (C.realPt w) (C.realPt w') : ℝ))) ∧ (∀ y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.ψ (symplOH S T (finW S T y) (finW S T y')) = cexp (-(π * I * ((∑ k, EF C.X (y k) (y' k) : ℚ) : ℂ)))) ∧ (∀ w u : WO S T, IsRealPt w → IsFinPt u → symplO S T w u = 0 ∧ symplO S T u w = 0) ∧ (∀ w : WO S T, symplO S T w w = 0) ∧ (∀ w w' w'' : WO S T, symplO S T (w + w') w'' = symplO S T w w'' + symplO S T w' w'' ∧ symplO S T w w' = -symplO S T w' w) ∧ (∀ (h : GA D S) (g : GA D T) (w w' : WO S T), symplO S T (actO S T h g w) (actO S T h g w') = symplO S T w w') ∧ ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.realPt (ratW T S yᵀ) = embR C.X y ∧ IsFinPt (finW S T y) ∧ IsRealPt (ratW T S yᵀ - finW S T y) ∧ ∀ y', finW S T (y + y') = finW S T y + finW S T y' := by
  first | exact @GlobalTheory.FormMatch.forms_match | exact GlobalTheory.FormMatch.forms_match | (intros; apply GlobalTheory.FormMatch.forms_match <;> assumption)
