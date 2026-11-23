import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebung
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (h : (p : k) = 0) (G : PDivGroup p k), Module.finrank k (LinearMap.range ((relFrob h G.dual).app 1 : (frobTwist h G.dual).A 1 →ₐ[k] G.dual.A 1).toLinearMap) + Module.finrank k (LinearMap.ker ((verschiebung h G).app 1 : G.A 1 →ₐ[k] (frobTwist h G).A 1).toLinearMap) = Module.finrank k (G.A 1) := by
  first | exact @GlobalTheory.PDivGroup.finrank_range_relFrob_dual_add_finrank_ker_verschiebung | exact GlobalTheory.PDivGroup.finrank_range_relFrob_dual_add_finrank_ker_verschiebung | (intros; apply GlobalTheory.PDivGroup.finrank_range_relFrob_dual_add_finrank_ker_verschiebung <;> assumption)
