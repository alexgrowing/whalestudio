import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCharEqZeroOfKillsVerschiebung
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_char_eq_zero_of_kills_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R ((frobTwist h G).A n)), (∀ a : G.A n, χ ((verschiebung h G).app n a) = 0) → χ ^ p = 0 := by
  first | exact @GlobalTheory.PDivGroup.pow_char_eq_zero_of_verschiebung | exact GlobalTheory.PDivGroup.pow_char_eq_zero_of_verschiebung | (intros; apply GlobalTheory.PDivGroup.pow_char_eq_zero_of_verschiebung <;> assumption)
