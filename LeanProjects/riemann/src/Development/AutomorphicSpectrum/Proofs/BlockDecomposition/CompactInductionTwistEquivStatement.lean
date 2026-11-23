import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistEquiv
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactInduction_twist_equiv : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (χ : G →* ℂˣ), IsOpen (χ.ker : Set G) →
    Nonempty ((twist (cInd H σ) χ).Equiv (cInd H (twist σ (χ.comp H.subtype)))) := by
  first | exact @GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv | exact GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv | (intros; apply GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv <;> assumption)
