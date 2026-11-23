import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgRankZeroHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.PhiPG0
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_pg_rank_zero_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG0 k := by
  first | exact @GlobalTheory.CompanionTheory.MirLevi.phiPG0_holds | exact GlobalTheory.CompanionTheory.MirLevi.phiPG0_holds | (intros; apply GlobalTheory.CompanionTheory.MirLevi.phiPG0_holds <;> assumption)
