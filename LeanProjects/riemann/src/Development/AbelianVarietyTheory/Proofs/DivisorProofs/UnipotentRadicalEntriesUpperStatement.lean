import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalEntriesUpper
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_entries_upper : ∀ (R : Type) [CommRing R] (n i : ℕ) (hi : i + 1 ≤ n) (g : GL (Fin n) R), g ∈ GlobalTheory.SmGL.unipRad R (blockIndex hi) →
    ∀ l j : Fin n, (g.1 - 1) l j ≠ 0 → (l : ℕ) ≤ i ∧ (l : ℕ) < j := by
  first | exact @GlobalTheory.LeviBlockFrame.sub_one_ne_zero_imp | exact GlobalTheory.LeviBlockFrame.sub_one_ne_zero_imp | (intros; apply GlobalTheory.LeviBlockFrame.sub_one_ne_zero_imp <;> assumption)
