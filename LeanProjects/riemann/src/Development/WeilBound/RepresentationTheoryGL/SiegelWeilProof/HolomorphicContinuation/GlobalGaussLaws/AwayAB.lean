import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayAA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 100000

namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

theorem triv_mul {θ : InfFam D} {τ : D.what₂.Tau} {a b : G D n} (ha : IsTrivAt θ τ a) (hb : IsTrivAt θ τ b) :
    IsTrivAt θ τ (a * b) := by
  unfold IsTrivAt at *
  rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, compAt_mul', ha, hb, Matrix.mul_one]

theorem triv_inv {θ : InfFam D} {τ : D.what₂.Tau} {a : G D n} (ha : IsTrivAt θ τ a) : IsTrivAt θ τ a⁻¹ := by
  unfold IsTrivAt at *
  have h : compAt θ τ (mat a⁻¹) * compAt θ τ (mat a) = 1 := by
    rw [← compAt_mul', ← GlobalTheory.StdUnn.LeftInvSect.mat_mul, inv_mul_cancel, GlobalTheory.StdUnn.LeftInvSect.mat_one, compAt_one']
  rwa [ha, Matrix.mul_one] at h

theorem triv_one {θ : InfFam D} {τ : D.what₂.Tau} : IsTrivAt θ τ (1 : G D n) := by
  unfold IsTrivAt; rw [GlobalTheory.StdUnn.LeftInvSect.mat_one, compAt_one']

theorem eq_one_of_triv_ι {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι) {y : GR n}
    (hy : IsTrivAt θ τ (ι y)) : y = 1 := by
  unfold IsTrivAt at hy
  rw [(hι.2 y).1] at hy
  have h1 : mR y = 1 := by
    have h2 : (mR y).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
        (1 : M2 n).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      rw [Matrix.submatrix_one_equiv]; exact hy
    have := congrArg (fun M => Matrix.submatrix M finSumFinEquiv finSumFinEquiv) h2
    simpa using this
  exact Subtype.ext (Units.ext h1)

theorem uniq_dec {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι) {a a' : G D n} {y y' : GR n}
    (ha : IsTrivAt θ τ a) (ha' : IsTrivAt θ τ a') (h : a * ι y = a' * ι y') : y = y' := by
  have h2 : ι (y * y'⁻¹) = a⁻¹ * a' := by
    rw [map_mul, map_inv]
    calc ι y * (ι y')⁻¹ = a⁻¹ * (a * ι y) * (ι y')⁻¹ := by group
      _ = a⁻¹ * (a' * ι y') * (ι y')⁻¹ := by rw [h]
      _ = a⁻¹ * a' := by group
  have : y * y'⁻¹ = 1 := eq_one_of_triv_ι hι (by rw [h2]; exact triv_mul (triv_inv ha) ha')
  exact mul_inv_eq_one.mp this

theorem blocks_of_away {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {M : Mx D (n + n) (n + n)}
    (hM : ∀ τ', τ' ≠ τ → compAt θ τ' M = 1) (hMf : M.map (finPart D) = 1) {α β γ δ : Matrix (Fin n) (Fin n) ℂ}
    (hτ : compAt θ τ M = blk4 α β γ δ) :
    ∃ A B C E' : Mx D n n, M = blk4 A B C E' ∧ compAt θ τ A = α ∧ compAt θ τ B = β ∧ compAt θ τ C = γ ∧
      compAt θ τ E' = δ ∧ (∀ τ', τ' ≠ τ → compAt θ τ' A = 1 ∧ compAt θ τ' B = 0 ∧ compAt θ τ' C = 0 ∧ compAt θ τ' E' = 1) ∧
      A.map (finPart D) = 1 ∧ B.map (finPart D) = 0 ∧ C.map (finPart D) = 0 ∧ E'.map (finPart D) = 1 := by
  obtain ⟨B, E', hBE⟩ := GlobalTheory.CompanionTheory.SwUnf.SmallCell.exists_blocks M
  set A := blkA M
  set C := GlobalTheory.CompanionTheory.SwUnf.lowerC M
  refine ⟨A, B, C, E', hBE, ?_⟩
  have h0 := hτ
  rw [hBE, component_block_matrix] at h0
  obtain ⟨e1, e2, e3, e4⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h0
  refine ⟨e1, e2, e3, e4, fun τ' hτ' => ?_, ?_⟩
  · have h1 := hM τ' hτ'
    rw [hBE, component_block_matrix, ← GlobalTheory.StdUnn.Model.block_matrix_one] at h1
    obtain ⟨f1, f2, f3, f4⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h1
    exact ⟨f1, f2, f3, f4⟩
  · have h1 := hMf
    rw [hBE, GlobalTheory.StdUnn.Frame.block_matrix_map, ← GlobalTheory.StdUnn.Model.block_matrix_one] at h1
    obtain ⟨f1, f2, f3, f4⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h1
    exact ⟨f1, f2, f3, f4⟩

theorem eq_of_comps {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {X Y : Mx D n n} (hτ : compAt θ τ X = compAt θ τ Y)
    (hτ' : ∀ τ', τ' ≠ τ → compAt θ τ' X = compAt θ τ' Y) (hf : X.map (finPart D) = Y.map (finPart D)) : X = Y := by
  refine mx_ext hθ (fun τ'' => ?_) hf
  by_cases h : τ'' = τ
  · subst h; exact hτ
  · exact hτ' τ'' h

end PositivityTheory.Rg.Sw.Glob.AW
