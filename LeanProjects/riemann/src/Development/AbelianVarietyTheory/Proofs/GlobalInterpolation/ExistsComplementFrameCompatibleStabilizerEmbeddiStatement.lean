import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsComplementFrameCompatibleStabilizerEmbeddi
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
theorem _root_.GlobalTheory.T.exists_complement_frame_compatible_stabilizerEmbedding : ∀ (P Q P' Q' M M' : ℕ), P' + Q' + 1 = P + Q → M' = P' + Q' → ∀ (G : Matrix (Fin M) (Fin M) ℂ) (G' : Matrix (Fin M') (Fin M') ℂ) (B : Matrix (Fin M) (Fin M') ℂ) (x : Fin M → ℂ) (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), Aᴴ * Formalism.UG.Jpq P Q * A = G → Bᴴ * G * B = G' → G'.det ≠ 0 → (Bᴴ * G) *ᵥ x = 0 → star (A *ᵥ x) ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ (A *ᵥ x) ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb (A *ᵥ x) j → ∃ A' : Matrix (Fin P' ⊕ Fin Q') (Fin M') ℂ, A'ᴴ * Formalism.UG.Jpq P' Q' * A' = G' ∧ ∀ (g : Matrix (Fin M) (Fin M) ℂ) (g' : Matrix (Fin M') (Fin M') ℂ) (t : UpqT P Q) (t' : UpqT P' Q'), g *ᵥ x = x → g * B = B * g' → UpqT.mat t * A = A * g → UpqT.mat t' * A' = A' * g' → t = j t' := by
  first | exact @GlobalTheory.StabFrameCompat.exists_compatible_frame | exact GlobalTheory.StabFrameCompat.exists_compatible_frame | (intros; apply GlobalTheory.StabFrameCompat.exists_compatible_frame <;> assumption)
