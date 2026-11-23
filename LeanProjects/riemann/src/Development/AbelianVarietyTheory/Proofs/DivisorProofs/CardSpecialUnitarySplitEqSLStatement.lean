import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSpecialUnitarySplitEqSL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_special_unitary_split_eq_SL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), Unr E → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ¬ (extIdeal (E := E) v).IsPrime → Nat.card (suMat (𝓞 E ⧸ extIdeal v) (resConj v) r) = Nat.card (Matrix.SpecialLinearGroup (Fin r) (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal)) := by
  first | exact @GlobalTheory.TamOne.card_suMat_split | exact GlobalTheory.TamOne.card_suMat_split | (intros; apply GlobalTheory.TamOne.card_suMat_split <;> assumption)
