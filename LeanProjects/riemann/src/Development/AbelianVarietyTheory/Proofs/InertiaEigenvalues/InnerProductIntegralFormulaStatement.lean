import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerProductIntegralFormula
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFormulaOfKernel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_product_integral_formula : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), ∃ c : ℝ, 0 < c ∧ ∀ u u' : (R.HV i t).H, ⟪u, u'⟫_ℂ = (c : ℂ) * ∫ h in R.fdV i t, ⟪R.extV i t u h, R.extV i t u' h⟫_ℂ ∂(R.νV i t) ∧ ∀ a a' : (R.cV i).W, IntegrableOn (fun h => star ⟪a, R.extV i t u h⟫_ℂ * ⟪a', R.extV i t u' h⟫_ℂ) (R.fdV i t) (R.νV i t) := by
  first | exact @GlobalTheory.AdelicL2Norm.norm_eq_integral | exact GlobalTheory.AdelicL2Norm.norm_eq_integral | (intros; apply GlobalTheory.AdelicL2Norm.norm_eq_integral <;> assumption)
