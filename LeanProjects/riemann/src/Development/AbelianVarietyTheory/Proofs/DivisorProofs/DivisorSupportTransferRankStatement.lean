import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorSupportTransferRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_support_transfer_rank : ∀ {D : D7} (V V' : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), V'.rank = V.rank → IsPrimeIdem P e f → SuppF V f α → DivAt V e ϖ d α → ∃ α' : GA D V', SuppF V' f α' ∧ DivAt V' e ϖ d α' := by
  first | exact @GlobalTheory.DivMove.exists_divAt_of_rank_eq | exact GlobalTheory.DivMove.exists_divAt_of_rank_eq | (intros; apply GlobalTheory.DivMove.exists_divAt_of_rank_eq <;> assumption)
