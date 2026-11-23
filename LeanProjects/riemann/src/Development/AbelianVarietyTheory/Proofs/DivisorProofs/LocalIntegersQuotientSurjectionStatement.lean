import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIntegersQuotientSurjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_integers_quotient_surjection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ ρ : intLoc (maximalRealSubfield E) E v →+* 𝓞 E ⧸ extIdeal v, Function.Surjective ρ ∧ (∀ x, ρ (intLocIncl v x) = Ideal.Quotient.mk (extIdeal v) x) ∧ ∀ z, ρ z = 0 ↔ z ∈ (extIdeal v).map (intLocIncl v) := by
  first | exact @GlobalTheory.TamOne.exists_residueMap_intLoc | exact GlobalTheory.TamOne.exists_residueMap_intLoc | (intros; apply GlobalTheory.TamOne.exists_residueMap_intLoc <;> assumption)
