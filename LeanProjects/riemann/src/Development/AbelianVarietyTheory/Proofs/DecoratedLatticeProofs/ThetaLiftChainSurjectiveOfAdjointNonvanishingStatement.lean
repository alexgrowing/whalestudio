import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSurjectiveOfAdjointNonvanishing
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChain_surjective_of_adjoint_nonvanishing : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ChainUp D → OntoAll D := by
  first | exact @GlobalTheory.ChainOnto.ontoAll_of_chainUp | exact GlobalTheory.ChainOnto.ontoAll_of_chainUp | (intros; apply GlobalTheory.ChainOnto.ontoAll_of_chainUp <;> assumption)
