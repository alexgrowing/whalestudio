import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRepresentationOfFinitePair
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_representation_of_finite_pair : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), FinPair V μ 𝓕 → ∃ ρ, IsReg V μ 𝓕 ρ := by
  first | exact @GlobalTheory.QuotRegular.exists_isReg | exact GlobalTheory.QuotRegular.exists_isReg | (intros; apply GlobalTheory.QuotRegular.exists_isReg <;> assumption)
