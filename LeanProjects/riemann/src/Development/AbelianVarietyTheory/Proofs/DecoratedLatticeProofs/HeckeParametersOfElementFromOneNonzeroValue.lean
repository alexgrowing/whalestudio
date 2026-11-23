import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainEigenPartHasHeckeParametersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageCuspFormValueMemFullSphericalHeckeEigenpartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ChainOnto.parOfVal_of_parts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ParOfVal D := by
  intro hP D hM hL c hc j hj s hs x w B hv hf
  obtain ⟨e, he⟩ := GlobalTheory.T.stageCuspFormValue_mem_fullSphericalHecke_eigenpart hP D hM hL c hc j hj s hs x w B hv hf
  exact (GlobalTheory.T.thetaChain_eigenPart_has_heckeParameters hP D c hc j hj s hs x e he).2 w B hv hf
