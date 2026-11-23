import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEachStepSplitPlaceWithoutExcludedParams
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UpNeNSOfUpNe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainNS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_each_step_splitPlace_without_excludedParams : ∀ D : D7, ChainNS D := by
  first | exact @GlobalTheory.ChainNS.chainNS_holds | exact GlobalTheory.ChainNS.chainNS_holds | (intros; apply GlobalTheory.ChainNS.chainNS_holds <;> assumption)
