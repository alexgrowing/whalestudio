import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueRingStructure
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_ring_structure : PositivityTheory.SiegelWeilFormula.Gunr.RvRing := by
  first | exact @GlobalTheory.CompanionTheory.RvRingPf.rvRing | exact GlobalTheory.CompanionTheory.RvRingPf.rvRing | (intros; apply GlobalTheory.CompanionTheory.RvRingPf.rvRing <;> assumption)
