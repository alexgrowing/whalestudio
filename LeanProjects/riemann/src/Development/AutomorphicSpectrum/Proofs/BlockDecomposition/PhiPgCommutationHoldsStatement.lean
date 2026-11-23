import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgCommutationHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_pg_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG k := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.phiPG | exact GlobalTheory.CompanionTheory.BZPhiPG.phiPG | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.phiPG <;> assumption)
