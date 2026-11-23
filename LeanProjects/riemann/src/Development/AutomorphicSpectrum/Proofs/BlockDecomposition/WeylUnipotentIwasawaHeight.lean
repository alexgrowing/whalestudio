import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.HeightNu
open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem exists_blocks {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    ∃ a b c d : Matrix (Fin n) (Fin n) R, M = blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  unfold blk4
  rw [Matrix.fromBlocks_toBlocks]
  ext i j
  simp

theorem absA_det_ad {D : D7} {n : ℕ} (a : GL (Fin n) (AE D)) :
    absA D (Matrix.GeneralLinearGroup.det (ad a)) =
      (absA D (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  have h : (Matrix.GeneralLinearGroup.det (ad a) : (AE D)ˣ) =
      (conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det a⁻¹ : (AE D)ˣ) : (AE D)ˣ) := by
    apply Units.ext
    change (adj (a⁻¹).1 : Mx D n n).det = _
    unfold adj
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (cA D) (a⁻¹).1).symm
  rw [h, GlobalTheory.DiagThetaRule.absA_conj, map_inv, map_inv]

theorem levi_unip_blocks {D : D7} {n : ℕ} {p : G D n} (hp : p ∈ P D n) (a : GL (Fin n) (AE D))
    (ha : blkA (mat p) = a.1) : ∃ b, mat p = blk4 a.1 b 0 (adj (a⁻¹).1) := by
  obtain ⟨m, u, b, hpe, hm, hu⟩ := exists_levi_unip hp a ha
  refine ⟨a.1 * b, ?_⟩
  rw [hpe, mat_mul, hm, hu, submatrix_fromBlocks_mul]
  simp [-Matrix.coe_units_inv]

theorem mat_w_nb {D : D7} {n : ℕ} {nb : hermA D n → G D n} (hnb : IsNMap nb) {w : G D n}
    (hw : mat w = blk4 0 1 (-1) 0) (c : hermA D n) : mat (w * nb c) = blk4 0 1 (-1) (-c.1) := by
  rw [mat_mul, hw, hnb, submatrix_fromBlocks_mul]
  simp

theorem lower_row : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHeight H → ∀ (nb : hermA D n → G D n), IsNMap nb → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ c : hermA D n, ∃ (d : GL (Fin n) (AE D)) (k : G D n) (k₁ k₂ k₃ k₄ : Mx D n n), k ∈ K D n ∧ mat k = blk4 k₁ k₂ k₃ k₄ ∧ d.1 * k₃ = -1 ∧ d.1 * k₄ = -c.1 ∧ (H (w * nb c))⁻¹ = absA D (Matrix.GeneralLinearGroup.det d) := by
  intro D n H hH nb hnb w hw c
  obtain ⟨p, hp, k, hk, e⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n (w * nb c)
  obtain ⟨a, ha⟩ := exists_blkA hp
  obtain ⟨b, hmp⟩ := levi_unip_blocks hp a ha
  obtain ⟨k₁, k₂, k₃, k₄, hk4⟩ := exists_blocks (mat k)
  have h2 := mat_w_nb hnb hw c
  rw [e, mat_mul, hmp, hk4, submatrix_fromBlocks_mul] at h2
  obtain ⟨-, -, h3, h4⟩ := blockMatrixTwoByTwoFin_injective h2
  rw [Matrix.zero_mul, zero_add] at h3 h4
  refine ⟨ad a, k, k₁, k₂, k₃, k₄, hk, hk4, h3, h4, ?_⟩
  rw [e, hH p hp a ha k hk, absA_det_ad]
end GlobalTheory.CompanionTheory.HeightNu
