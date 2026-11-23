import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDualWeylProductSpanOfFactorwiseDualWeyl
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_dualWeylProductSpan_of_factorwise_dualWeyl : ∀ (k : Type) [Field k] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (ν : ι → Fin N → ℕ) (P : MvPolynomial (BVar N ι) k), (∀ τ, toBlock k N τ P ∈ dualWeyl (MvPolynomial (OVar N τ) k) N N (ν τ)) → P ∈ nabK k N ν := by
  first | exact @GlobalTheory.HighWtEmb.mem_nabK_of_toBlock | exact GlobalTheory.HighWtEmb.mem_nabK_of_toBlock | (intros; apply GlobalTheory.HighWtEmb.mem_nabK_of_toBlock <;> assumption)
