import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverse
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.CartStd

variable {D : D7}

theorem tauE_star_eq (τ : D.what₂.Tau) (x : D.host.E) : tauE D τ (star x) = star (tauE D τ x) := by
  have := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) ℂ) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  rw [blk4, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  rfl

theorem stdJ_mul_self (n : ℕ) : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) * blk4 0 1 (-1) 0 = -1 := by
  rw [submatrix_fromBlocks_mul]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul, neg_zero]
  rw [blk4, show Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) ℂ) 0 0 (-1) = -1 by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]]
  rw [show ((-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
      -((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) from rfl,
    Matrix.submatrix_one_equiv]

theorem stdJ_conjTranspose (n : ℕ) :
    (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ)ᴴ = -blk4 0 1 (-1) 0 := by
  unfold blk4
  rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose,
    show -((Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm) = (-(Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm from rfl, Matrix.fromBlocks_neg]
  simp

theorem map_Jst (τ : D.what₂.Tau) (n : ℕ) : (Jst D n).map (tauE D τ) = blk4 0 1 (-1) 0 := by
  unfold Jst blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  have h1 : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = -1 := by
    rw [← RingHom.mapMatrix_apply, map_neg, map_one]
  simp [h1]

end GlobalTheory.CartStd

namespace GlobalTheory.CartStd

theorem isCartanInv_stdInv : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ s : RealMat (dblSp A),
    IsStdInv A μ s → ∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (s τ) := by
  intro D A μ hμ s hs τ
  obtain ⟨hgram, hdet, -⟩ := GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  set f := tauE D τ with hf
  set T := (Tm A μ).map f with hT
  set J : Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) ℂ := blk4 0 1 (-1) 0 with hJ
  set z := f μ with hz
  have hstar : Function.Semiconj f star star := fun x => tauE_star_eq τ x
  have hTG : Tᴴ * gramAt D (dblSp A) τ * T = z • J := by
    have h := congrArg (fun M => M.map f) hgram
    simp only [Matrix.map_mul] at h
    rw [Matrix.conjTranspose_map f hstar] at h
    rw [show gramAt D (dblSp A) τ = (dblSp A).gram.map f from rfl, h, hJ, ← map_Jst τ A.rank]
    ext i j
    simp [Matrix.smul_apply, hz, hf]
  have hTdet : IsUnit T.det := by
    rw [hT, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map f
  set U := T⁻¹ with hU
  have hTU : T * U = 1 := Matrix.mul_nonsing_inv T hTdet
  have hUT : U * T = 1 := Matrix.nonsing_inv_mul T hTdet
  have hUhTh : Uᴴ * Tᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hTU, Matrix.conjTranspose_one]

  have hz0 : z ≠ 0 := (map_ne_zero f).2 hμ.1
  have hzc : star z = -z := by rw [hz, ← tauE_star_eq, hμ.2, map_neg]
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
  have hzz : z * z = -(((‖z‖ : ℝ) : ℂ) ^ 2) := by
    have h1 := Complex.mul_conj z
    rw [Complex.normSq_eq_norm_sq, ← Complex.star_def, hzc] at h1
    push_cast at h1
    linear_combination -h1
  set c := z / ((‖z‖ : ℝ) : ℂ) with hc
  have hcc : c * c = -1 := by
    rw [hc]; field_simp; linear_combination hzz
  have hcstar : star c = -c := by
    rw [hc, star_div₀, hzc, Complex.star_def, Complex.conj_ofReal, neg_div]
  have hzc' : z * c = -((‖z‖ : ℝ) : ℂ) := by
    rw [hc]; field_simp; linear_combination hzz

  set S := c • J with hS
  have hJJ : J * J = -1 := stdJ_mul_self _
  have hSS : S * S = 1 := by
    rw [hS, smul_mul_smul_comm, hcc, hJJ, neg_one_smul, neg_neg]
  have hSh : Sᴴ = S := by
    rw [hS, Matrix.conjTranspose_smul, hJ, stdJ_conjTranspose, hcstar, smul_neg, neg_smul, neg_neg]
  have hsS : s τ = T * S * U := by
    have h := hs τ
    rw [show stdInv A.rank μ τ = S from rfl] at h
    calc s τ = s τ * T * U := by rw [Matrix.mul_assoc, hTU, Matrix.mul_one]
      _ = T * S * U := by rw [h]
  have hG : gramAt D (dblSp A) τ = Uᴴ * (z • J) * U := by
    rw [← hTG]
    calc gramAt D (dblSp A) τ = (Uᴴ * Tᴴ) * gramAt D (dblSp A) τ * (T * U) := by
          rw [hUhTh, hTU, Matrix.one_mul, Matrix.mul_one]
      _ = Uᴴ * (Tᴴ * gramAt D (dblSp A) τ * T) * U := by simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsS]
    calc T * S * U * (T * S * U) = T * S * (U * T) * S * U := by simp only [Matrix.mul_assoc]
      _ = T * U := by rw [hUT, Matrix.mul_one, Matrix.mul_assoc T S S, hSS, Matrix.mul_one]
      _ = 1 := hTU
  · rw [hsS, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh]
    have hSJS : S * (z • J) * S = z • J := by
      rw [hS, smul_mul_smul_comm, hJJ, smul_mul_smul_comm, Matrix.neg_mul, Matrix.one_mul,
        show c * z * c = -z by linear_combination z * hcc, neg_smul, smul_neg, neg_neg]
    calc Uᴴ * (S * Tᴴ) * gramAt D (dblSp A) τ * (T * S * U)
        = Uᴴ * (S * (Tᴴ * gramAt D (dblSp A) τ * T) * S) * U := by simp only [Matrix.mul_assoc]
      _ = gramAt D (dblSp A) τ := by rw [hTG, hSJS, hG]
  · have hGs : gramAt D (dblSp A) τ * s τ = Uᴴ * (((‖z‖ : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)) * U := by
      rw [hsS]
      calc gramAt D (dblSp A) τ * (T * S * U) = (Uᴴ * Tᴴ) * gramAt D (dblSp A) τ * (T * S * U) := by
            rw [hUhTh, Matrix.one_mul]
        _ = Uᴴ * ((Tᴴ * gramAt D (dblSp A) τ * T) * S) * U := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hTG, hS, smul_mul_smul_comm, hJJ, hzc', neg_smul, smul_neg, neg_neg]
    rw [hGs]
    have hpos : (0 : ℂ) < ((‖z‖ : ℝ) : ℂ) := Complex.zero_lt_real.2 (norm_pos_iff.2 hz0)
    refine (Matrix.PosDef.one.smul hpos).conjTranspose_mul_mul_same ?_
    intro x y hxy
    have h := congrArg T.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hTU] using h

end GlobalTheory.CartStd
