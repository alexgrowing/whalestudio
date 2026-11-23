import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusSubmoduleMulLeftImageMemSelfDualStableLatti
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_submoduleMulLeftImage_mem_selfDualStableLattices : ∀ (K : UQ) (B : InvAlg K) (x : B.A), ∀ t ∈ B.T, ∀ L ∈ B.X x, mulLat K.O (t : B.A) L ∈ B.X x := by
  first | exact @GlobalTheory.UnitLemma.TorusAction.torus_mem_X | exact GlobalTheory.UnitLemma.TorusAction.torus_mem_X | (intros; apply GlobalTheory.UnitLemma.TorusAction.torus_mem_X <;> assumption)
