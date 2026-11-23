import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFrobeniusPullbackCotangentModVersc
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additive_frobeniusPullback_cotangent_mod_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ w : Cot K ((frobTwist h G).A 1), ∃ (β : (frobTwist h G).A 1) (w' : Cot K (G.A 1)), cobOne K (G.A 1) ((relFrob h G).app 1 β) = 0 ∧ dUnit K β = w + cotMap ((verschiebung h G).app 1) w' := by
  first | exact @GlobalTheory.PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq | exact GlobalTheory.PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq | (intros; apply GlobalTheory.PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq <;> assumption)
