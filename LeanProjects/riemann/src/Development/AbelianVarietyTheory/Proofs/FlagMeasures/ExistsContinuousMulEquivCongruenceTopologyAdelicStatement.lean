import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMulEquivCongruenceTopologyAdelic
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousMulEquiv_congruenceTopology_adelicUnitary : ∀ (I : AutInst), ∃ e : I.Gf ≃ₜ* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J, (∀ x, ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J (e x) : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) = (I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) ∧ ∀ x, x ∈ I.Kset ↔ GlobalTheory.Mem.Vol.StabHat I.F (I.L : Set (Fin I.n → I.E)) ((I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) := by
  first | exact @GlobalTheory.CongTop.Swap.exists_continuousMulEquiv_adelic | exact GlobalTheory.CongTop.Swap.exists_continuousMulEquiv_adelic | (intros; apply GlobalTheory.CongTop.Swap.exists_continuousMulEquiv_adelic <;> assumption)
