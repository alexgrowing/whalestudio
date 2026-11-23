import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighestWeightAtConjugateEmbeddingRevNeg
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeightAt_conjugate_embedding_rev_neg : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ), a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i)) := by
  first | exact @GlobalTheory.hwAt_conj_swap | exact GlobalTheory.hwAt_conj_swap | (intros; apply GlobalTheory.hwAt_conj_swap <;> assumption)
