import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardReductionUnitaryEqSuMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_reduction_unitary_eq_suMat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), Set.ncard ((fun g : Matrix (Fin r) (Fin r) (𝓞 E) => g.map (Ideal.Quotient.mk (v.asIdeal.map (algebraMap _ (𝓞 E))))) '' {g | g.det - 1 ∈ v.asIdeal.map (algebraMap _ (𝓞 E)) ∧ ∀ a b, (gᵀ * g.map (IsCMField.ringOfIntegersComplexConj E) - 1) a b ∈ v.asIdeal.map (algebraMap _ (𝓞 E))}) = Nat.card (suMat (𝓞 E ⧸ extIdeal v) (resConj v) r) := by
  first | exact @GlobalTheory.TamOneInert.main | exact GlobalTheory.TamOneInert.main | (intros; apply GlobalTheory.TamOneInert.main <;> assumption)
