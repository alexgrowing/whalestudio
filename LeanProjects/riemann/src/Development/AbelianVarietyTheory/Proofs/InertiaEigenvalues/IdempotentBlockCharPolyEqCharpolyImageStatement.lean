import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockCharPolyEqCharpolyImage
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentBlockCharPoly_eq_charpoly_image : ∀ {K : Type} [Field K] {n t : ℕ} (e : Matrix (Fin n) (Fin n) K), e * e = e → e.rank = t → ∃ (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), b * a = 1 ∧ a * b = e ∧ ∀ M : Matrix (Fin n) (Fin n) K, blockPol e (e * M * e) = (b * M * a).charpoly := by
  first | exact @GlobalTheory.BlockCharpoly.blockPol_eq_charpoly | exact GlobalTheory.BlockCharpoly.blockPol_eq_charpoly | (intros; apply GlobalTheory.BlockCharpoly.blockPol_eq_charpoly <;> assumption)
