import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamsTrivialBoundRapidDecayStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem parBoundW_of_parBound {D : D7} (h : ParBound D) : ParBoundW D := by
  intro c hc j hj s hs u B hu
  exact GlobalTheory.LiftPole.Bounded.mono (h c hc j hj s hs u B hu) (by linarith)

theorem parBoundW (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) (hL : LevFacts D) : ParBoundW D :=
  parBoundW_of_parBound (GlobalTheory.T.thetaChain_heckeParams_trivialBound_rapidDecay hP D hL)

end GlobalTheory.ChainOnto
