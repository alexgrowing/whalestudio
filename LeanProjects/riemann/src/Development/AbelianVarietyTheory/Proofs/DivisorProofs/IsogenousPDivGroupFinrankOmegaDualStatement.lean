import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDual
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → Function.Injective (T.map q) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧ Module.finrank k G.omega = Module.finrank k H.omega ∧ Module.finrank k G.dual.omega = Module.finrank k H.dual.omega := by
  first | exact @GlobalTheory.Dieu.isog_finrank_omega | exact GlobalTheory.Dieu.isog_finrank_omega | (intros; apply GlobalTheory.Dieu.isog_finrank_omega <;> assumption)
