import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviPiTensorRepresentationIsIrreducible
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockEmbeddingFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTensorBlockExt
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviPiTensorRepresentation_isIrreducible : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, Simple (lam c)) → (leviTensor b lam).IsIrreducible := by
  first | exact @GlobalTheory.HcIrr.leviTensor_isIrreducible | exact GlobalTheory.HcIrr.leviTensor_isIrreducible | (intros; apply GlobalTheory.HcIrr.leviTensor_isIrreducible <;> assumption)
