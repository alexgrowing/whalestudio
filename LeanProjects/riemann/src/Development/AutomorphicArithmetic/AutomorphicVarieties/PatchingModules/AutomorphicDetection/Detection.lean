import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DetAsm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.EllClosed
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.detection :
    UpperTheory.V.Pa.Detection := by
  intro l _ F n x k hl hε S _ hS z hz h0
  refine UpperTheory.V.Pa.Det.detAsm k hl hε z hz fun σ hσ => ?_
  exact closure_minimal (t := {σ : F.G₀ | ell k x.A σ z = 0}) h0 (UpperTheory.V.Pa.Det.ellClosed k z hz) (hS hσ)
