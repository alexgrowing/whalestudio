import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabEmbClosed

theorem isClosedEmbedding_conj_fromBlocks {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m (n ⊕ Unit) ℂ) (N : Matrix (n ⊕ Unit) m ℂ) (hNM : N * M = 1) :
    IsClosedEmbedding
      (fun X : Matrix n n ℂ => M * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * N) := by
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun Y : Matrix m m ℂ => (N * Y * M).toBlocks₁₁) ?_ ?_ ?_
  · intro X
    have : N * (M * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * N) * M
        = fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) := by
      calc _ = (N * M) * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * (N * M) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hNM, Matrix.one_mul, Matrix.mul_one]
    simp only [this, toBlocks_fromBlocks₁₁]
  · have h : Continuous fun Y : Matrix m m ℂ => N * Y * M :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact h.matrix_submatrix Sum.inl Sum.inl
  · exact (continuous_const.matrix_mul
      (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
        continuous_const)).matrix_mul continuous_const

theorem isClosedEmbedding_of_isStabEmb : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ (x₀ : Fin P ⊕ Fin Q → ℂ), star x₀ ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x₀ ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb x₀ j → IsClosedEmbedding j := by
  intro P Q P' Q' hd x₀ hx j hj
  obtain ⟨C, hC, hCx, hj⟩ := hj
  obtain ⟨N, B, hNM, hMN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hd hx hC hCx
  have key : ∀ g : UpqT P' Q', (j g).mat =
      C.fromCols (replicateCol Unit x₀) * fromBlocks g.mat 0 0 (1 : Matrix Unit Unit ℂ) * N := by
    intro g
    obtain ⟨h1, h2⟩ := hj g
    have h3 : (j g).mat * replicateCol Unit x₀ = replicateCol Unit x₀ := by
      rw [← replicateCol_mulVec, h1]
    have h4 : (j g).mat * C.fromCols (replicateCol Unit x₀) =
        C.fromCols (replicateCol Unit x₀) * fromBlocks g.mat 0 0 (1 : Matrix Unit Unit ℂ) := by
      rw [mul_fromCols, fromCols_mul_fromBlocks, h2, h3]
      simp
    rw [← h4, Matrix.mul_assoc, hMN, Matrix.mul_one]
  refine IsClosedEmbedding.of_comp
    (GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P) (Q := Q)).isEmbedding ?_
  have := (isClosedEmbedding_conj_fromBlocks _ N hNM).comp
    (GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P') (Q := Q'))
  convert this using 1
  funext g
  exact key g

end GlobalTheory.StabEmbClosed
