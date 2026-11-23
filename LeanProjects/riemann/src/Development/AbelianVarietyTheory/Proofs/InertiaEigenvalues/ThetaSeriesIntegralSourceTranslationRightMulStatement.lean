import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralSourceTranslationRightMul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_integralSourceTranslation_right_mul : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω → ∀ (Q : Finset (Pl D.host.E)), B.admitted Q → ∀ hb : ∀ PP : ↥Q, GL (Fin S.rank) (kP PP.1), ∃ hQ, SuppAt (idem Q) S hQ ∧ ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank), series B.F ω (B.vecAt Q fun PP y => φ PP (y * (hb PP).val)) h P = series B.F ω (B.vecAt Q φ) (h * hQ) P := by
  first | exact @GlobalTheory.SourceTrans.exists_series_vecAt_translate_eq_series_mul | exact GlobalTheory.SourceTrans.exists_series_vecAt_translate_eq_series_mul | (intros; apply GlobalTheory.SourceTrans.exists_series_vecAt_translate_eq_series_mul <;> assumption)
