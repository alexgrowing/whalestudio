import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittDecompositionIsotropicFrameEisensteinDiction
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch GlobalTheory.ResidueEisenstein
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittDecomposition_isotropicFrameEisenstein_dictionary : ∀ (D : D7) (V V₀ : HSp D) (r : ℕ) (d : HypDec V V₀ (r + 1)), IsAniso V₀ → ∀ l : Lvl V, l.Good → HasIw d l.K → DataJ D.sp.cm.sig V.gram d.e d.e' l.L l.c (fun g => (iwAbs (absDet d) l.K g : ℝ)) ∧ (∃ T, IsRepsJ D.sp.cm.sig V.gram d.e T) ∧ ∀ T, IsRepsJ D.sp.cm.sig V.gram d.e T → ∀ (g : GA D V) (s : ℂ), sphericalEisensteinSeriesOnGroup d l.K g s = ∑' t : T, (((iwAbs (absDet d) l.K (t.1.1 * g) : ℝ≥0) : ℝ) : ℂ) ^ (s + ((V.rank : ℂ) - (r + 1)) / 2) := by
  first | exact @GlobalTheory.ResidueDictionary.dict | exact GlobalTheory.ResidueDictionary.dict | (intros; apply GlobalTheory.ResidueDictionary.dict <;> assumption)
