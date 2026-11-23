import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClosedEmbeddingOfIsStabilizerEmbeddingUpq
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_of_isStabilizerEmbeddingUpq : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ (x₀ : Fin P ⊕ Fin Q → ℂ), star x₀ ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x₀ ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb x₀ j → IsClosedEmbedding j := by
  first | exact @GlobalTheory.StabEmbClosed.isClosedEmbedding_of_isStabEmb | exact GlobalTheory.StabEmbClosed.isClosedEmbedding_of_isStabEmb | (intros; apply GlobalTheory.StabEmbClosed.isClosedEmbedding_of_isStabEmb <;> assumption)
