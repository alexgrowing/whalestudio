import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIsogenyOmegaAndDualSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_isogeny_omega_and_dual_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → Function.Surjective (omegaMap G H q) → Function.Surjective (omegaMap H.dual G.dual (dualHom G H q)) → IsIso q := by
  first | exact @GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective | exact GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective | (intros; apply GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective <;> assumption)
