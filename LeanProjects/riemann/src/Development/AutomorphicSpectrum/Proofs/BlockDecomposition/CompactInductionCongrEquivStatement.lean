import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionCongrEquiv
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactInduction_congr_equiv : ∀ {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (H : Subgroup G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'),
    σ.Equiv σ' → Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  first | exact @GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd | exact GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd | (intros; apply GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd <;> assumption)
