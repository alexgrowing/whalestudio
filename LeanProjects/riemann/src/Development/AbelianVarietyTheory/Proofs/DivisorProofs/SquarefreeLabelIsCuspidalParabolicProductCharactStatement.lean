import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeLabelIsCuspidalParabolicProductCharact
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefreeLabel_isCuspidalParabolicProductCharacter : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (O : LabelMap K C) (r : ℕ) (τ : FDRep ℂ (GL (Fin r) K)) (f : K[X]), Simple τ → HasLabelO O τ f → Squarefree f → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => τ.character x) := by
  first | exact @GlobalTheory.SqfreeCuspProd.isCuspProdChar_of_squarefree | exact GlobalTheory.SqfreeCuspProd.isCuspProdChar_of_squarefree | (intros; apply GlobalTheory.SqfreeCuspProd.isCuspProdChar_of_squarefree <;> assumption)
