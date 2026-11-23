import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Formalism.LocalRingCardinality.Lemmas
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.PairingOpNorm
open Matrix

theorem pairing_eq {K : Type} [Field K] (c n : ℕ) (g : (Fin c → K) →ₗ[K] Module.Dual K (Fin n → K))
    (y : Fin c → K) (F : Fin n → K) :
    g y F = F ⬝ᵥ (LinearMap.toMatrix (Pi.basisFun K (Fin c)) (Pi.basisFun K (Fin n)).dualBasis g *ᵥ y) := by
  have h := LinearMap.toMatrix_mulVec_repr (Pi.basisFun K (Fin c)) (Pi.basisFun K (Fin n)).dualBasis g y
  rw [show (Pi.basisFun K (Fin c)).repr y = y from rfl] at h
  rw [h]
  conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr F]
  simp [dotProduct, map_sum, Basis.dualBasis_repr, mul_comm]

theorem continuous_cnorm {ι : Type} [Fintype ι] : Continuous (Formalism.HermitianLatticesTheory.cnorm : (ι → ℂ) → ℝ) := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  fun_prop

theorem cnorm_nonneg {ι : Type} [Fintype ι] (u : ι → ℂ) : 0 ≤ Formalism.HermitianLatticesTheory.cnorm u := Real.sqrt_nonneg _

theorem bilin_bound {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (c n : ℕ)
    (X : Matrix (Fin c) (Fin c) ℂ) (X0 : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin n) (Fin c) ℂ)
    (v : InfinitePlace K) (C : ℝ)
    (h : ∀ (y : Fin c → K) (F : Fin n → K), ‖(fun j => v.embedding (F j)) ⬝ᵥ (S *ᵥ fun i => v.embedding (y i))‖ ≤
      C * Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ fun j => v.embedding (F j)) * Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ fun i => v.embedding (y i)))
    (u : Fin n → ℂ) (z : Fin c → ℂ) :
    ‖u ⬝ᵥ (S *ᵥ z)‖ ≤ C * Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ u) * Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ z) := by
  have hv : v.IsComplex := IsTotallyComplex.isComplex v
  have hd : DenseRange (Prod.map (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)))
      (Pi.map (fun _ : Fin c => (v.embedding : K → ℂ)))) :=
    DenseRange.prodMap (DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v hv))
      (DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v hv))
  have key : ∀ p : (Fin n → ℂ) × (Fin c → ℂ),
      ‖p.1 ⬝ᵥ (S *ᵥ p.2)‖ ≤ C * Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ p.1) * Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ p.2) := by
    intro p
    induction p using hd.induction_on with
    | hp =>
      apply isClosed_le
      · exact (Continuous.dotProduct continuous_fst
          (Continuous.matrix_mulVec continuous_const continuous_snd)).norm
      · exact (continuous_const.mul (continuous_cnorm.comp
          (Continuous.matrix_mulVec continuous_const continuous_fst))).mul
          (continuous_cnorm.comp (Continuous.matrix_mulVec continuous_const continuous_snd))
    | ih q => exact h q.2 q.1
  exact key (u, z)

end GlobalTheory.PairingOpNorm

namespace GlobalTheory.PairingOpNorm
open Matrix

theorem opNormAt_pairing_sq_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (c n : ℕ) (X : InfinitePlace K → Matrix (Fin c) (Fin c) ℂ) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (g : (Fin c → K) →ₗ[K] Module.Dual K (Fin n → K)) (v : InfinitePlace K) (A : ℝ), IsUnit (X v).det → IsUnit (X0 v).det → (∀ y F, v (g y F) ^ 2 ≤ Real.exp A * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin c)) X v y ^ 2 * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2) → Formalism.HN.opNormAt (Pi.basisFun K (Fin c)) X (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v g ^ 2 ≤ Real.exp A := by
  intro K _ _ _ _ c n X X0 g v A hX hX0 hb
  set σ : K →+* ℂ := v.embedding with hσ
  set S : Matrix (Fin n) (Fin c) ℂ :=
    (LinearMap.toMatrix (Pi.basisFun K (Fin c)) (Pi.basisFun K (Fin n)).dualBasis g).map σ with hS
  set C : ℝ := Real.exp (A / 2) with hC
  have hC0 : 0 ≤ C := (Real.exp_pos _).le
  have hCsq : C ^ 2 = Real.exp A := by rw [hC, sq, ← Real.exp_add]; ring_nf
  have hnorm : ∀ {m : ℕ} (Y : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ) (x : Fin m → K),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin m)) Y v x = Formalism.HermitianLatticesTheory.cnorm ((Y v)⁻¹ *ᵥ fun i => σ (x i)) := by
    intro m Y x; rfl
  have hK : ∀ (y : Fin c → K) (F : Fin n → K), ‖(fun j => σ (F j)) ⬝ᵥ (S *ᵥ fun i => σ (y i))‖ ≤
      C * Formalism.HermitianLatticesTheory.cnorm ((X0 v)⁻¹ *ᵥ fun j => σ (F j)) * Formalism.HermitianLatticesTheory.cnorm ((X v)⁻¹ *ᵥ fun i => σ (y i)) := by
    intro y F
    have e1 : (fun j => σ (F j)) ⬝ᵥ (S *ᵥ fun i => σ (y i)) = σ (g y F) := by
      rw [pairing_eq, RingHom.map_dotProduct]
      congr 1
      funext i
      exact (RingHom.map_mulVec σ _ y i).symm
    rw [e1, hσ, InfinitePlace.norm_embedding_eq]
    have h1 := hb y F
    rw [hnorm, hnorm] at h1
    have hpos : 0 ≤ C * Formalism.HermitianLatticesTheory.cnorm ((X0 v)⁻¹ *ᵥ fun j => σ (F j)) *
        Formalism.HermitianLatticesTheory.cnorm ((X v)⁻¹ *ᵥ fun i => σ (y i)) :=
      mul_nonneg (mul_nonneg hC0 (cnorm_nonneg _)) (cnorm_nonneg _)
    refine (pow_le_pow_iff_left₀ (apply_nonneg v _) hpos (by norm_num : (2:ℕ) ≠ 0)).1 ?_
    calc v (g y F) ^ 2 ≤ _ := h1
      _ = _ := by rw [mul_pow, mul_pow, hCsq]; ring
  have hB := bilin_bound c n (X v) (X0 v) S v C hK
  have hinv : (Formalism.HN.dualFrame X0 v)⁻¹ = (X0 v)ᵀ := by
    unfold Formalism.HN.dualFrame
    rw [Matrix.nonsing_inv_nonsing_inv]
    rwa [Matrix.det_transpose]
  unfold Formalism.HN.opNormAt
  rw [hinv]
  suffices hT : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((X0 v)ᵀ * S * X v))‖ ≤ C by
    rw [← hCsq]
    exact pow_le_pow_left₀ (norm_nonneg _) hT 2
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 (fun ξ => ?_)
  set M : Matrix (Fin n) (Fin c) ℂ := (X0 v)ᵀ * S * X v with hM
  set w : Fin c → ℂ := WithLp.ofLp ξ with hw
  set m : Fin n → ℂ := M *ᵥ w with hm
  have hTx : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) ξ‖ = Formalism.HermitianLatticesTheory.cnorm m := by
    simp [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, EuclideanSpace.norm_eq,
      Formalism.HermitianLatticesTheory.cnorm, hm, hw]
  have hξ : ‖ξ‖ = Formalism.HermitianLatticesTheory.cnorm w := by
    simp [EuclideanSpace.norm_eq, Formalism.HermitianLatticesTheory.cnorm, hw]
  rw [hTx, hξ]
  have h1 := hB ((X0 v) *ᵥ star m) ((X v) *ᵥ w)
  have i0 : (X0 v)⁻¹ *ᵥ ((X0 v) *ᵥ star m) = star m := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hX0, Matrix.one_mulVec]
  have i1 : (X v)⁻¹ *ᵥ ((X v) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hX, Matrix.one_mulVec]
  rw [i0, i1] at h1
  have e2 : ((X0 v) *ᵥ star m) ⬝ᵥ (S *ᵥ ((X v) *ᵥ w)) = star m ⬝ᵥ m := by
    rw [hm, hM, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hsum : 0 ≤ ∑ i, ‖m i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcn : Formalism.HermitianLatticesTheory.cnorm m ^ 2 = ∑ i, ‖m i‖ ^ 2 := by
    unfold Formalism.HermitianLatticesTheory.cnorm; rw [Real.sq_sqrt hsum]
  have e3 : ‖star m ⬝ᵥ m‖ = Formalism.HermitianLatticesTheory.cnorm m ^ 2 := by
    rw [hcn]
    have : star m ⬝ᵥ m = ((∑ i, ‖m i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Complex.star_def, Complex.conj_mul']
    rw [this, Complex.norm_of_nonneg hsum]
  have e4 : Formalism.HermitianLatticesTheory.cnorm (star m) = Formalism.HermitianLatticesTheory.cnorm m := by
    simp [Formalism.HermitianLatticesTheory.cnorm]
  rw [e2, e3, e4] at h1
  rcases (cnorm_nonneg m).eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg hC0 (cnorm_nonneg w)
  · refine le_of_mul_le_mul_left ?_ h0
    nlinarith [h1]

end GlobalTheory.PairingOpNorm
