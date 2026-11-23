import Mathlib
import Formalism.QuotientMetricDivisors.HeightBoundExactNorms
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionThirdStepMean
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean

open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

namespace OperatorNormFrames

theorem cnorm_eq {n : ℕ} (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [Formalism.HermitianLatticesTheory.cnorm]

theorem cnorm_nonneg {n : ℕ} (u : Fin n → ℂ) : 0 ≤ Formalism.HermitianLatticesTheory.cnorm u := Real.sqrt_nonneg _

theorem cnorm_star {n : ℕ} (u : Fin n → ℂ) : Formalism.HermitianLatticesTheory.cnorm (star u) = Formalism.HermitianLatticesTheory.cnorm u := by
  first
    | simp [Formalism.HermitianLatticesTheory.cnorm, norm_star]
    | simp [Formalism.HermitianLatticesTheory.cnorm, Complex.norm_conj]

theorem norm_dot_le {n : ℕ} (y w : Fin n → ℂ) :
    ‖y ⬝ᵥ w‖ ≤ Formalism.HermitianLatticesTheory.cnorm y * Formalism.HermitianLatticesTheory.cnorm w := by
  have h1 : ‖y ⬝ᵥ w‖ ≤ ∑ i, ‖y i‖ * ‖w i‖ := by
    first
      | simpa [dotProduct, norm_mul] using norm_sum_le Finset.univ fun i => y i * w i
      | simpa [Matrix.dotProduct, norm_mul] using norm_sum_le Finset.univ fun i => y i * w i
  exact h1.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)

theorem star_dot_self {n : ℕ} (w : Fin n → ℂ) :
    star w ⬝ᵥ w = ((Formalism.HermitianLatticesTheory.cnorm w ^ 2 : ℝ) : ℂ) := by
  have h : Formalism.HermitianLatticesTheory.cnorm w ^ 2 = ∑ i, ‖w i‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  rw [h]
  push_cast
  first
    | simp only [dotProduct, Pi.star_apply]
    | simp only [Matrix.dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
    | exact Complex.conj_mul' (w i)
    | exact_mod_cast Complex.conj_mul' (w i)
    | exact RCLike.conj_mul (w i)

theorem opNorm_le_iff {a D : ℕ} (A : Matrix (Fin D) (Fin a) ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ ≤ c ↔
      ∀ (x : Fin a → ℂ) (y : Fin D → ℂ),
        ‖y ⬝ᵥ A.mulVec x‖ ≤ c * Formalism.HermitianLatticesTheory.cnorm x * Formalism.HermitianLatticesTheory.cnorm y := by
  have hT : ∀ x : Fin a → ℂ,
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) (WithLp.toLp 2 x)‖ =
        Formalism.HermitianLatticesTheory.cnorm (A.mulVec x) := by
    intro x
    rw [cnorm_eq]
    simp [Matrix.toEuclideanLin_apply]
  constructor
  · intro h x y
    have h2 : Formalism.HermitianLatticesTheory.cnorm (A.mulVec x) ≤ c * Formalism.HermitianLatticesTheory.cnorm x := by
      rw [← hT, cnorm_eq x]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
    calc ‖y ⬝ᵥ A.mulVec x‖ ≤ Formalism.HermitianLatticesTheory.cnorm y * Formalism.HermitianLatticesTheory.cnorm (A.mulVec x) := norm_dot_le _ _
      _ ≤ Formalism.HermitianLatticesTheory.cnorm y * (c * Formalism.HermitianLatticesTheory.cnorm x) :=
          mul_le_mul_of_nonneg_left h2 (cnorm_nonneg y)
      _ = c * Formalism.HermitianLatticesTheory.cnorm x * Formalism.HermitianLatticesTheory.cnorm y := by ring
  · intro h
    refine ContinuousLinearMap.opNorm_le_bound _ hc fun z => ?_
    obtain ⟨x, rfl⟩ : ∃ x, z = WithLp.toLp 2 x := ⟨WithLp.ofLp z, by simp⟩
    rw [hT, ← cnorm_eq]
    have h3 := h x (star (A.mulVec x))
    rw [star_dot_self, cnorm_star] at h3
    have h4 : ‖((Formalism.HermitianLatticesTheory.cnorm (A.mulVec x) ^ 2 : ℝ) : ℂ)‖ = Formalism.HermitianLatticesTheory.cnorm (A.mulVec x) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h4] at h3
    have hN := cnorm_nonneg (A.mulVec x)
    have hX := cnorm_nonneg x
    nlinarith [mul_nonneg hc hX]

def pmat {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) : Matrix (Fin D) (Fin a) ℂ :=
  Matrix.of fun k i => v.embedding (B (Pi.single i 1) (Pi.single k 1))

theorem pairC_eq {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (x : Fin a → ℂ) (y : Fin D → ℂ) :
    pairC v B x y = y ⬝ᵥ (pmat v B).mulVec x := by
  first
    | simp only [pairC, pmat, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    | simp only [pairC, pmat, Matrix.dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem toMatrix_dual {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) :
    (LinearMap.toMatrix (Pi.basisFun K (Fin a)) (Pi.basisFun K (Fin D)).dualBasis B).map v.embedding =
      pmat v B := by
  ext k i
  simp [pmat, LinearMap.toMatrix_apply]

theorem dot_frames {a D : ℕ} (Y : Matrix (Fin D) (Fin D) ℂ) (M : Matrix (Fin D) (Fin a) ℂ)
    (X : Matrix (Fin a) (Fin a) ℂ) (x : Fin a → ℂ) (y : Fin D → ℂ) :
    y ⬝ᵥ (Yᵀ * M * X).mulVec x = (Y.mulVec y) ⬝ᵥ M.mulVec (X.mulVec x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem opNormAt_dual_eq {K : Type} [Field K] [NumberField K] [StarRing K] {a D : ℕ}
    (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ v, IsUnit (XE v).det) (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (v : InfinitePlace K) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) XM (Pi.basisFun K (Fin D)).dualBasis
              (Formalism.HN.dualFrame XE) v B =
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((XE v)ᵀ * pmat v B * XM v))‖ := by
  simp only [Formalism.HN.opNormAt, Formalism.HN.dualFrame]
  rw [toMatrix_dual, Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hE v)]

theorem mul_inv_mulVec {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y.det) (x : Fin n → ℂ) :
    Y.mulVec (Y⁻¹.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hY, Matrix.one_mulVec]

theorem inv_mul_mulVec {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y.det) (x : Fin n → ℂ) :
    Y⁻¹.mulVec (Y.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hY, Matrix.one_mulVec]

end OperatorNormFrames

open OperatorNormFrames

theorem frobenius_norm_rational : FnormRat := by
  unfold FnormRat
  intro K _ _ _ n X v x y
  have hx : (fun i => v.embedding (x i)) = Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v x := by
    funext i
    show v.embedding (x i) = v.embedding ((Pi.basisFun K (Fin n)).repr x i)
    rw [Pi.basisFun_repr]
  have hy : (fun i => v.embedding (y i)) = Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v y := by
    funext i
    show v.embedding (y i) = v.embedding ((Pi.basisFun K (Fin n)).repr y i)
    rw [Pi.basisFun_repr]
  refine ⟨?_, ?_, ?_⟩
  · simp only [fnorm, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord]
    rw [hx]
  · simp only [fmaj, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord]
    rw [hx, hy]
  · simp only [fnorm, fmaj]
    rw [← star_dot_self]
    rfl

theorem operator_norm_dual : OpNormDual := by
  unfold OpNormDual
  intro K _ _ _ a D XM XE hM hE B v c hc
  rw [opNormAt_dual_eq XM XE hE B v, opNorm_le_iff _ c hc]
  constructor
  · intro h x y
    have h1 := h ((XM v)⁻¹.mulVec x) ((XE v)⁻¹.mulVec y)
    rw [dot_frames, mul_inv_mulVec _ (hE v), mul_inv_mulVec _ (hM v)] at h1
    rw [pairC_eq]
    exact h1
  · intro h x y
    have h1 := h ((XM v).mulVec x) ((XE v).mulVec y)
    rw [pairC_eq] at h1
    rw [dot_frames]
    simpa only [fnorm, inv_mul_mulVec _ (hM v), inv_mul_mulVec _ (hE v)] using h1

theorem chain_spectrum : ChainSpec := by
  unfold ChainSpec
  refine ⟨fun m C Kj φ => ⟨?_, fun j => ?_⟩, fun R _ m c Kj => ⟨?_, fun j => ?_⟩⟩
  · first | rfl | simp [chainFun]
  · first | rfl | simp [chainFun]
  · first | rfl | simp [chainMat]
  · first | rfl | simp [chainMat]

namespace OperatorNormFrames

theorem filter_succ {m : ℕ} (j : Fin m) :
    Finset.univ.filter (fun i : Fin m => i.castSucc < j.succ) =
      insert j (Finset.univ.filter (fun i : Fin m => i.castSucc < j.castSucc)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.lt_iff_val_lt_val, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
  omega

theorem prod_filter_succ {m : ℕ} (k : Fin m → ℝ) (j : Fin m) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin m => i.castSucc < j.succ), k i =
      k j * ∏ i ∈ Finset.univ.filter (fun i : Fin m => i.castSucc < j.castSucc), k i := by
  rw [filter_succ, Finset.prod_insert (by simp)]

theorem filter_last {m : ℕ} :
    Finset.univ.filter (fun i : Fin m => i.castSucc < Fin.last m) = Finset.univ := by
  first
    | exact Finset.filter_true_of_mem fun i _ => Fin.castSucc_lt_last i
    | ext i; simp [Fin.castSucc_lt_last]

theorem filter_zero {m : ℕ} :
    Finset.univ.filter (fun i : Fin m => i.castSucc < (0 : Fin (m + 1))) = ∅ := by
  first
    | exact Finset.filter_false_of_mem fun i _ => Fin.not_lt_zero _
    | ext i; simp

end OperatorNormFrames

open OperatorNormFrames in
theorem composition_norm : CompNorm := by
  unfold CompNorm
  intro m C _ Kj k hk hK φ
  have key : ∀ i : Fin (m + 1), ‖chainFun Kj i φ‖ ≤
      (∏ j ∈ Finset.univ.filter (fun j : Fin m => j.castSucc < i), k j) * ‖φ‖ := by
    intro i
    induction i using Fin.induction with
    | zero =>
      have h0 : chainFun Kj 0 φ = φ := by first | rfl | simp [chainFun]
      simp only [h0, filter_zero, Finset.prod_empty, one_mul, le_refl]
    | succ j ih =>
      have h1 : chainFun Kj j.succ φ = Kj j (chainFun Kj j.castSucc φ) := by
        first | rfl | simp [chainFun]
      rw [prod_filter_succ, h1, mul_assoc]
      exact (hK j _).trans (mul_le_mul_of_nonneg_left ih (hk j))
  simpa only [filter_last] using key (Fin.last m)

namespace OperatorNormFrames

theorem minOver_le {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) (p : Ix) : minOver f ≤ f p := by
  unfold minOver
  apply Finset.inf'_le
  exact Finset.mem_univ p

theorem exists_minOver {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) : ∃ p, minOver f = f p := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Ix)) f
  exact ⟨i, hi⟩

theorem le_minOver {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) (a : ℝ) (h : ∀ p, a ≤ f p) :
    a ≤ minOver f := by
  obtain ⟨q, hq⟩ := exists_minOver f
  rw [hq]
  exact h q

end OperatorNormFrames

open OperatorNormFrames in
theorem successive_minimum_log : SminLog := by
  unfold SminLog
  intro Ix J _ _ _ κ lam hκ hlam
  have hpos : ∀ p, 0 < ∏ j, lam j p := fun p => Finset.prod_pos fun j _ => hlam j p
  have hlog : ∀ p, Real.log (∏ j, lam j p) = ∑ j, Real.log (lam j p) := by
    intro p
    first
      | exact Real.log_prod fun j _ => (hlam j p).ne'
      | exact Real.log_prod _ _ fun j _ => (hlam j p).ne'
  obtain ⟨q, hq0⟩ := exists_minOver (fun p => ∏ j, lam j p)
  have hq : minOver (fun p => ∏ j, lam j p) = ∏ j, lam j q := hq0
  have hmin : ∀ p, ∏ j, lam j q ≤ ∏ j, lam j p := by
    intro p
    rw [← hq]
    exact minOver_le _ p
  refine ⟨?_, fun p => ?_, ⟨q, by rw [hq]⟩, ?_⟩
  · rw [hq]
    exact mul_pos hκ (hpos q)
  · exact mul_le_mul_of_nonneg_left (minOver_le _ p) hκ.le
  · rw [hq, Real.log_mul hκ.ne' (hpos q).ne', hlog q]
    congr 1
    apply le_antisymm
    · apply le_minOver
      intro p
      show ∑ j, Real.log (lam j q) ≤ ∑ j, Real.log (lam j p)
      rw [← hlog q, ← hlog p]
      exact Real.log_le_log (hpos q) (hmin p)
    · exact minOver_le _ q

namespace OperatorNormFrames

theorem cnorm_sq_mulVec {n d : ℕ} (Z : Matrix (Fin d) (Fin n) ℂ) (y : Fin n → ℂ) :
    ((Formalism.HermitianLatticesTheory.cnorm (Z.mulVec y) ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ (Zᴴ * Z).mulVec y := by
  rw [← star_dot_self, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

theorem cnorm_le_of_orth {n : ℕ} (p q : Fin n → ℂ) (h : star p ⬝ᵥ q = 0) :
    Formalism.HermitianLatticesTheory.cnorm p ≤ Formalism.HermitianLatticesTheory.cnorm (p + q) := by
  have h2 : star q ⬝ᵥ p = 0 := by
    have e : star q ⬝ᵥ p = star (star p ⬝ᵥ q) := by
      first
        | simp [dotProduct, mul_comm]
        | simp [Matrix.dotProduct, mul_comm]
    rw [e, h, star_zero]
  have key : ((Formalism.HermitianLatticesTheory.cnorm (p + q) ^ 2 : ℝ) : ℂ) =
      ((Formalism.HermitianLatticesTheory.cnorm p ^ 2 + Formalism.HermitianLatticesTheory.cnorm q ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_add, ← star_dot_self, ← star_dot_self, ← star_dot_self, star_add]
    first
      | rw [add_dotProduct, dotProduct_add, dotProduct_add, h, h2]
      | rw [Matrix.add_dotProduct, Matrix.dotProduct_add, Matrix.dotProduct_add, h, h2]
    ring
  have key' := Complex.ofReal_injective key
  nlinarith [cnorm_nonneg p, cnorm_nonneg (p + q), sq_nonneg (Formalism.HermitianLatticesTheory.cnorm q)]

theorem quot_rep {n D : ℕ} (Hc X0 : Matrix (Fin n) (Fin n) ℂ) (h0 : IsUnit X0.det)
    (hH : (X0⁻¹)ᴴ * X0⁻¹ = Hc) (Pc : Matrix (Fin D) (Fin n) ℂ) (XQ : Matrix (Fin D) (Fin D) ℂ)
    (hQ : IsUnit XQ.det) (hG : (XQ⁻¹)ᴴ * XQ⁻¹ = (Pc * Hc⁻¹ * Pcᴴ)⁻¹) (y : Fin D → ℂ) :
    ∃ x : Fin n → ℂ, Pc.mulVec x = y ∧ fnorm X0 x = fnorm XQ y ∧
      ∀ u : Fin n → ℂ, Pc.mulVec u = 0 → fmaj X0 x u = 0 := by
  generalize hM : Pc * Hc⁻¹ * Pcᴴ = M at hG
  have hX0i : IsUnit (X0⁻¹).det := Matrix.isUnit_nonsing_inv_det X0 h0
  have hXQi : IsUnit (XQ⁻¹).det := Matrix.isUnit_nonsing_inv_det XQ hQ
  have hHcU : IsUnit Hc.det := by
    rw [isUnit_iff_ne_zero] at hX0i ⊢
    rw [← hH, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (star_ne_zero.2 hX0i) hX0i
  have hMiU : IsUnit (M⁻¹).det := by
    rw [isUnit_iff_ne_zero] at hXQi ⊢
    rw [← hG, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (star_ne_zero.2 hXQi) hXQi
  have hMU : IsUnit M.det := Matrix.isUnit_nonsing_inv_det_iff.mp hMiU
  have hHcH : Hcᴴ = Hc := by
    rw [← hH, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hHiH : (Hc⁻¹)ᴴ = Hc⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hHcH]
  have hMH : Mᴴ = M := by
    rw [← hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hHiH, Matrix.mul_assoc]
  have hGH : (M⁻¹)ᴴ = M⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hMH]
  have hx : Hc⁻¹ *ᵥ (Pcᴴ *ᵥ (M⁻¹ *ᵥ y)) = (Hc⁻¹ * Pcᴴ * M⁻¹) *ᵥ y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hNN : (X0⁻¹ * (Hc⁻¹ * Pcᴴ * M⁻¹))ᴴ * (X0⁻¹ * (Hc⁻¹ * Pcᴴ * M⁻¹)) = (XQ⁻¹)ᴴ * XQ⁻¹ := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (X0⁻¹)ᴴ X0⁻¹, hH,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHiH, hGH]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hHcU]
    rw [← Matrix.mul_assoc Pc, ← Matrix.mul_assoc (Pc * Hc⁻¹), hM, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hMU, Matrix.one_mul]
  have hA : (X0⁻¹ * (Hc⁻¹ * Pcᴴ * M⁻¹))ᴴ * X0⁻¹ = M⁻¹ * Pc := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hH, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHiH, hGH]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHcU, Matrix.mul_one]
  refine ⟨Hc⁻¹ *ᵥ (Pcᴴ *ᵥ (M⁻¹ *ᵥ y)), ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM,
      Matrix.mul_nonsing_inv _ hMU, Matrix.one_mulVec]
  · rw [hx]
    have h1 : ((fnorm X0 ((Hc⁻¹ * Pcᴴ * M⁻¹) *ᵥ y) ^ 2 : ℝ) : ℂ) = ((fnorm XQ y ^ 2 : ℝ) : ℂ) := by
      show ((Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ ((Hc⁻¹ * Pcᴴ * M⁻¹) *ᵥ y)) ^ 2 : ℝ) : ℂ) =
        ((Formalism.HermitianLatticesTheory.cnorm (XQ⁻¹ *ᵥ y) ^ 2 : ℝ) : ℂ)
      rw [Matrix.mulVec_mulVec, cnorm_sq_mulVec, cnorm_sq_mulVec, hNN]
    have h2 := Complex.ofReal_injective h1
    have ha : 0 ≤ fnorm X0 ((Hc⁻¹ * Pcᴴ * M⁻¹) *ᵥ y) := cnorm_nonneg _
    have hb : 0 ≤ fnorm XQ y := cnorm_nonneg _
    exact le_antisymm (by nlinarith) (by nlinarith)
  · intro u hu
    rw [hx]
    show star (X0⁻¹ *ᵥ ((Hc⁻¹ * Pcᴴ * M⁻¹) *ᵥ y)) ⬝ᵥ (X0⁻¹ *ᵥ u) = 0
    rw [Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hA, ← Matrix.mulVec_mulVec, hu]
    simp

theorem quot_le {n D : ℕ} (Hc X0 : Matrix (Fin n) (Fin n) ℂ) (h0 : IsUnit X0.det)
    (hH : (X0⁻¹)ᴴ * X0⁻¹ = Hc) (Pc : Matrix (Fin D) (Fin n) ℂ) (XQ : Matrix (Fin D) (Fin D) ℂ)
    (hQ : IsUnit XQ.det) (hG : (XQ⁻¹)ᴴ * XQ⁻¹ = (Pc * Hc⁻¹ * Pcᴴ)⁻¹) (x : Fin n → ℂ) :
    fnorm XQ (Pc.mulVec x) ≤ fnorm X0 x := by
  obtain ⟨x0, hx0, hn, horth⟩ := quot_rep Hc X0 h0 hH Pc XQ hQ hG (Pc.mulVec x)
  have hw : Pc.mulVec (x - x0) = 0 := by
    rw [Matrix.mulVec_sub, hx0, sub_self]
  have h := horth _ hw
  rw [← hn]
  show Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ x0) ≤ Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ x)
  have e : X0⁻¹ *ᵥ x = X0⁻¹ *ᵥ x0 + X0⁻¹ *ᵥ (x - x0) := by
    rw [← Matrix.mulVec_add]
    congr 1
    abel
  rw [e]
  exact cnorm_le_of_orth _ _ h

end OperatorNormFrames

open OperatorNormFrames in
theorem quotient_metric_representation : QuotMetricRep := by
  unfold QuotMetricRep
  intro K _ _ _ n D H X0 h0 P hP XQ hQ v
  obtain ⟨hQu, hQe⟩ := hQ v
  exact ⟨fun x => quot_le (H.map v.embedding) (X0 v) (h0 v).1 (h0 v).2 (P.map v.embedding) (XQ v)
      hQu hQe x,
    fun y => quot_rep (H.map v.embedding) (X0 v) (h0 v).1 (h0 v).2 (P.map v.embedding) (XQ v)
      hQu hQe y⟩

namespace OperatorNormFrames

theorem dual_expand {K : Type} [Field K] {D : ℕ} (f : Module.Dual K (Fin D → K)) (e : Fin D → K) :
    f e = ∑ d, e d * f (Pi.single d 1) := by
  have he : e = ∑ d, e d • Pi.single d 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [he]
  simp [map_sum, map_smul]

theorem map_expand {K : Type} [Field K] {a D : ℕ} (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (φ : Fin a → K) (e : Fin D → K) : B φ e = ∑ i, φ i * B (Pi.single i 1) e := by
  have hφ : φ = ∑ i, φ i • Pi.single i 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hφ]
  simp [map_sum, map_smul, LinearMap.sum_apply]

theorem pairC_transfer {K : Type} [Field K] [NumberField K] {a b n D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (A : (Fin b → K) →ₗ[K] Module.Dual K (Fin n → K))
    (N : Matrix (Fin D) (Fin n) K) (C : Matrix (Fin b) (Fin a) K)
    (h : ∀ φ F, B φ (N.mulVec F) = A (C.mulVec φ) F) (x : Fin a → ℂ) (F : Fin n → ℂ) :
    pairC v B x ((N.map v.embedding).mulVec F) = pairC v A ((C.map v.embedding).mulVec x) F := by
  have key : ∀ i l, ∑ k, N k l * B (Pi.single i 1) (Pi.single k 1) =
      ∑ j, C j i * A (Pi.single j 1) (Pi.single l 1) := by
    intro i l
    have h1 := h (Pi.single i 1) (Pi.single l 1)
    rw [dual_expand (B (Pi.single i 1)), map_expand A] at h1
    simpa [Matrix.mulVec_single_one] using h1
  have hM : (N.map v.embedding)ᵀ * pmat v B = pmat v A * C.map v.embedding := by
    ext l i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, pmat, Matrix.of_apply]
    have := congrArg v.embedding (key i l)
    simp only [map_sum, map_mul] at this
    rw [this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [pairC_eq, pairC_eq, Matrix.mulVec_mulVec, ← hM, ← Matrix.mulVec_mulVec]
  conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem opNormAt_nonneg {K : Type} [Field K] [NumberField K] [StarRing K]
    {V ι W κ : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (v : InfinitePlace K) (φ : V →ₗ[K] W) :
    0 ≤ Formalism.HN.opNormAt b X b' X' v φ := norm_nonneg _

theorem exists_section {K : Type} [Field K] {n D : ℕ} (P : Matrix (Fin D) (Fin n) K)
    (hP : Function.Surjective P.mulVec) :
    ∃ ρ : (Fin D → K) →ₗ[K] (Fin n → K), ∀ y, P.mulVec (ρ y) = y := by
  obtain ⟨g, hg⟩ :=
    (Matrix.mulVecLin P).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hP)
  exact ⟨g, fun y => by simpa using LinearMap.congr_fun hg y⟩

end OperatorNormFrames

namespace OperatorNormFrames

def nrm {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

theorem nrm_mul_le {a b c : ℕ} (A : Matrix (Fin c) (Fin b) ℂ) (B : Matrix (Fin b) (Fin a) ℂ) :
    nrm (A * B) ≤ nrm A * nrm B := by
  unfold nrm
  have e : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A * B)) =
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).comp
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)) := by
    ext x : 1
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  rw [e]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem opNormAt_mulVecLin {K : Type} [Field K] [NumberField K] [StarRing K] {a b : ℕ}
    (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ)
    (v : InfinitePlace K) (N : Matrix (Fin b) (Fin a) K) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) X (Pi.basisFun K (Fin b)) X' v (Matrix.mulVecLin N) =
      nrm ((X' v)⁻¹ * N.map v.embedding * X v) := by
  have hN : LinearMap.toMatrix (Pi.basisFun K (Fin a)) (Pi.basisFun K (Fin b)) (Matrix.mulVecLin N) = N := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  simp only [Formalism.HN.opNormAt, nrm, hN]

theorem mulVecLin_ne_zero {K : Type} [Field K] {a b : ℕ} (N : Matrix (Fin b) (Fin a) K) (h : N ≠ 0) :
    Matrix.mulVecLin N ≠ 0 := by
  intro h0
  apply h
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h0
  simpa using this

end OperatorNormFrames

open OperatorNormFrames in
theorem composition_norm_at_place : CompNormAt := by
  intro K _ _ _ m c Xc hX Kj
  have key : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
      ∏ j : Fin m, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
        (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) := by
    intro v
    simp only [opNormAt_mulVecLin]
    have step : ∀ i : Fin (m + 1), nrm ((Xc i v)⁻¹ * (chainMat Kj i).map v.embedding * Xc 0 v) ≤
        ∏ j ∈ Finset.univ.filter (fun j : Fin m => j.castSucc < i),
          nrm ((Xc j.succ v)⁻¹ * (Kj j).map v.embedding * Xc j.castSucc v) := by
      intro i
      induction i using Fin.induction with
      | zero =>
        rw [filter_zero, Finset.prod_empty]
        have h1 : chainMat Kj 0 = 1 := rfl
        rw [h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
          Matrix.nonsing_inv_mul _ (hX 0 v)]
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
        simp
      | succ j ih =>
        rw [prod_filter_succ]
        have h1 : chainMat Kj j.succ = Kj j * chainMat Kj j.castSucc := rfl
        have h2 : (Xc j.succ v)⁻¹ * (chainMat Kj j.succ).map v.embedding * Xc 0 v =
            ((Xc j.succ v)⁻¹ * (Kj j).map v.embedding * Xc j.castSucc v) *
              ((Xc j.castSucc v)⁻¹ * (chainMat Kj j.castSucc).map v.embedding * Xc 0 v) := by
          rw [h1, Matrix.map_mul]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (Xc j.castSucc v), Matrix.mul_nonsing_inv _ (hX _ v), Matrix.one_mul]
        rw [h2]
        exact (nrm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
    have := step (Fin.last m)
    rwa [filter_last] at this
  refine ⟨key, fun hne => ?_⟩
  have hpos : ∀ v, 0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) := fun v =>
    Formalism.HN.PlaceOperatorNorms.opNormAt_pos _ _ _ _ (hX _) (hX _) v _ (mulVecLin_ne_zero _ hne)
  have hterm : ∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ^ 2) ≤
      ∑ j : Fin m, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
        (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ^ 2) := by
    intro v
    have hprod := (hpos v).trans_le (key v)
    have hne' : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
        (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ^ 2 ≠ 0 := by
      intro j hj
      exact pow_ne_zero 2 (Finset.prod_ne_zero_iff.1 hprod.ne' j hj)
    rw [← Real.log_prod hne', Finset.prod_pow]
    exact Real.log_le_log (pow_pos (hpos v) 2) (pow_le_pow_left₀ (hpos v).le (key v) 2)
  simp only [Formalism.HN.htMap]
  rw [← Finset.mul_sum, Finset.sum_comm]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hterm v) (by positivity)

namespace OperatorNormFrames

section G

variable {K : Type} [Field K] [NumberField K] {D : ℕ}

def gmap (v : InfinitePlace K) (Y : Matrix (Fin D) (Fin D) ℂ) (x : Fin D → K) :
    EuclideanSpace ℂ (Fin D) :=
  WithLp.toLp 2 (Y⁻¹.mulVec fun i => v.embedding (x i))

theorem map_mulVec_emb {n : ℕ} (v : InfinitePlace K) (N : Matrix (Fin D) (Fin n) K) (x : Fin n → K) :
    (fun i => v.embedding (N.mulVec x i)) = (N.map v.embedding).mulVec fun i => v.embedding (x i) := by
  ext i
  first
    | simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    | simp [Matrix.mulVec, Matrix.dotProduct, map_sum, map_mul]

end G

theorem place_bound {K : Type} [Field K] [NumberField K] [StarRing K] {n D a b : ℕ}
    (Xa : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (ha : ∀ v, IsUnit (Xa v).det)
    (Xb : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ) (hb : ∀ v, IsUnit (Xb v).det)
    (col : Matrix (Fin b) (Fin a) K)
    (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (h0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding)
    (P : Matrix (Fin D) (Fin n) K) (hP : Function.Surjective P.mulVec)
    (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hQ : IsQuotMetric P H XQ)
    (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hE : ∀ v, IsUnit (XE v).det)
    (ι : Matrix (Fin D) (Fin D) K) (hι : IsUnit ι.det)
    {Ix : Type} [Fintype Ix] (Qp : Ix → Submodule K (Fin D → K)) (hsup : (⨆ p, Qp p) = ⊤)
    (v : InfinitePlace K) (s : Ix → ℝ) (smin : ℝ) (hsmin : 0 < smin) (hs : ∀ p, smin ≤ s p)
    (hspec : ∀ p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v (ι.mulVec x) (ι.mulVec y) =
        ((s p : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XQ v x y)
    (Pt : (Fin b → K) →ₗ[K] Module.Dual K (Fin n → K))
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (hB : ∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt (col.mulVec φ) F)
    (p k : ℝ)
    (hp : Formalism.HN.opNormAt (Pi.basisFun K (Fin b)) Xb (Pi.basisFun K (Fin n)).dualBasis
      (Formalism.HN.dualFrame X0) v Pt ≤ p)
    (hk : Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) Xa (Pi.basisFun K (Fin b)) Xb v
      (Matrix.mulVecLin col) ≤ k) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) Xa (Pi.basisFun K (Fin D)).dualBasis
      (Formalism.HN.dualFrame XE) v B ≤ p * k / Real.sqrt smin := by
  have hp0 : 0 ≤ p := (opNormAt_nonneg _ _ _ _ _ _).trans hp
  have hk0 : 0 ≤ k := (opNormAt_nonneg _ _ _ _ _ _).trans hk
  have hr : 0 < Real.sqrt smin := Real.sqrt_pos.2 hsmin
  have hc : 0 ≤ p * k / Real.sqrt smin := div_nonneg (mul_nonneg hp0 hk0) hr.le
  have hstar : ∀ r : ℝ, star (r : ℂ) = (r : ℂ) := fun r => Complex.conj_ofReal r
  have hds : ∀ (x : Fin D → ℂ) (b : Ix → Fin D → ℂ), x ⬝ᵥ ∑ q, b q = ∑ q, x ⬝ᵥ b q := by
    intro x b
    simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  have hsd : ∀ (a' : Ix → Fin D → ℂ) (y : Fin D → ℂ), (∑ q, a' q) ⬝ᵥ y = ∑ q, a' q ⬝ᵥ y := by
    intro a' y
    simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hsm1 : ∀ (r : ℂ) (x y : Fin D → ℂ), (r • x) ⬝ᵥ y = r * (x ⬝ᵥ y) := by
    intro r x y
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hsm2 : ∀ (r : ℂ) (x y : Fin D → ℂ), x ⬝ᵥ (r • y) = r * (x ⬝ᵥ y) := by
    intro r x y
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmsm : ∀ (M : Matrix (Fin D) (Fin D) ℂ) (r : ℂ) (x : Fin D → ℂ), M *ᵥ (r • x) = r • (M *ᵥ x) := by
    intro M r x
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨ι', hι'def⟩ : ∃ M : Matrix (Fin D) (Fin D) ℂ, M = ι.map v.embedding := ⟨_, rfl⟩
  have hι'U : IsUnit ι'.det := by
    have h1 := RingHom.map_det v.embedding ι
    rw [RingHom.mapMatrix_apply] at h1
    rw [hι'def, ← h1, isUnit_iff_ne_zero]
    exact (map_ne_zero _).2 (isUnit_iff_ne_zero.mp hι)
  obtain ⟨GE, hGE⟩ : ∃ G : Matrix (Fin D) (Fin D) ℂ, G = ((XE v)⁻¹)ᴴ * (XE v)⁻¹ := ⟨_, rfl⟩
  obtain ⟨GQ, hGQ⟩ : ∃ G : Matrix (Fin D) (Fin D) ℂ, G = ((XQ v)⁻¹)ᴴ * (XQ v)⁻¹ := ⟨_, rfl⟩
  have hGEH : GEᴴ = GE := by
    rw [hGE, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hGQH : GQᴴ = GQ := by
    rw [hGQ, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  obtain ⟨A, hA⟩ : ∃ M : Matrix (Fin D) (Fin D) ℂ, M = ι'ᴴ * GE * ι' := ⟨_, rfl⟩
  have hAH : Aᴴ = A := by
    rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hGEH, Matrix.mul_assoc]
  have hherm : ∀ M : Matrix (Fin D) (Fin D) ℂ, Mᴴ = M → ∀ a' b' : Fin D → ℂ,
      star (M *ᵥ a') ⬝ᵥ b' = star a' ⬝ᵥ M *ᵥ b' := by
    intro M hM a' b'
    rw [Matrix.star_mulVec, hM, Matrix.dotProduct_mulVec]
  have hfm : ∀ (Y : Matrix (Fin D) (Fin D) ℂ) (a' b' : Fin D → ℂ),
      fmaj Y a' b' = star a' ⬝ᵥ ((Y⁻¹)ᴴ * Y⁻¹) *ᵥ b' := by
    intro Y a' b'
    show star (Y⁻¹ *ᵥ a') ⬝ᵥ (Y⁻¹ *ᵥ b') = _
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have hemb : ∀ x : Fin D → K,
      (fun i => v.embedding ((ι *ᵥ x) i)) = ι' *ᵥ (fun i => v.embedding (x i)) := by
    intro x
    rw [hι'def]
    exact map_mulVec_emb v ι x
  have hAform : ∀ a' b' : Fin D → ℂ, star (ι' *ᵥ a') ⬝ᵥ GE *ᵥ (ι' *ᵥ b') = star a' ⬝ᵥ A *ᵥ b' := by
    intro a' b'
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
  have hsj : ∀ j : Fin D, (fun i => v.embedding ((Pi.single j (1 : K) : Fin D → K) i)) = Pi.single j 1 := by
    intro j
    ext i
    by_cases h : i = j
    · subst h
      simp
    · simp [Pi.single_apply, h]
  have heig : ∀ q, ∀ x ∈ Qp q, A *ᵥ (fun i => v.embedding (x i)) =
      ((s q : ℝ) : ℂ) • (GQ *ᵥ (fun i => v.embedding (x i))) := by
    intro q x hx
    have hrow : star (fun i => v.embedding (x i)) ᵥ* A =
        ((s q : ℝ) : ℂ) • (star (fun i => v.embedding (x i)) ᵥ* GQ) := by
      ext j
      have h1 := hspec q x hx (Pi.single j 1)
      rw [← (frobenius_norm_rational K D XE v (ι *ᵥ x) (ι *ᵥ Pi.single j 1)).2.1,
        ← (frobenius_norm_rational K D XQ v x (Pi.single j 1)).2.1, hfm, hfm, ← hGE, ← hGQ, hemb, hemb,
        hAform, hsj, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec] at h1
      rw [Pi.smul_apply, smul_eq_mul]
      simpa [dotProduct, Pi.single_apply] using h1
    have h2 := congrArg star hrow
    simp only [Matrix.star_vecMul, star_star, star_smul, hAH, hGQH, hstar] at h2
    exact h2
  have hdec : ∀ z : Fin D → K, ∃ f : Ix → Fin D → K, (∀ q, f q ∈ Qp q) ∧ ∑ q, f q = z := by
    intro z
    have hz : z ∈ ⨆ q, Qp q := by
      rw [hsup]
      exact Submodule.mem_top
    classical
    refine Submodule.iSup_induction Qp
      (motive := fun z => ∃ f : Ix → Fin D → K, (∀ q, f q ∈ Qp q) ∧ ∑ q, f q = z) hz ?_ ?_ ?_
    · intro q x hx
      refine ⟨Pi.single q x, fun r => ?_, ?_⟩
      · by_cases h : r = q
        · subst h
          simpa using hx
        · rw [Pi.single_eq_of_ne h]
          exact Submodule.zero_mem _
      · rw [Finset.sum_eq_single q (fun r _ h => by simp [Pi.single_apply, h])
          (fun h => absurd (Finset.mem_univ q) h)]
        simp
    · exact ⟨0, fun q => Submodule.zero_mem _, by simp⟩
    · rintro x y ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
      exact ⟨f + g, fun q => Submodule.add_mem _ (hf q) (hg q), by simp [Finset.sum_add_distrib]⟩
  have hfQ : ∀ u : Fin D → ℂ, ((fnorm (XQ v) u ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ GQ *ᵥ u := by
    intro u
    rw [hGQ]
    exact cnorm_sq_mulVec _ _
  have hfE : ∀ u : Fin D → ℂ, ((fnorm (XE v) (ι' *ᵥ u) ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ A *ᵥ u := by
    intro u
    have e : fnorm (XE v) (ι' *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (((XE v)⁻¹ * ι') *ᵥ u) := by
      show Formalism.HermitianLatticesTheory.cnorm ((XE v)⁻¹ *ᵥ (ι' *ᵥ u)) = _
      rw [Matrix.mulVec_mulVec]
    rw [e, cnorm_sq_mulVec, hA, hGE, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have SPEC : ∀ w : Fin D → ℂ, smin * fnorm (XQ v) w ^ 2 ≤ fnorm (XE v) (ι' *ᵥ w) ^ 2 := by
    intro w
    choose f hf hfs using fun i : Fin D => hdec (Pi.single i 1)
    have hsum : ∀ i, ∑ q, (fun j => v.embedding (f i q j)) = (Pi.single i 1 : Fin D → ℂ) := by
      intro i
      ext j
      have h1 : (∑ q, f i q) j = (Pi.single i (1 : K) : Fin D → K) j := by rw [hfs i]
      rw [Finset.sum_apply] at h1
      rw [Finset.sum_apply]
      try simp only []
      rw [← map_sum v.embedding, h1]
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_apply, h]
    obtain ⟨W, hW⟩ : ∃ W : Ix → Fin D → ℂ,
        ∀ q, W q = ∑ i, w i • fun j => v.embedding (f i q j) := ⟨_, fun q => rfl⟩
    have hWsum : ∑ q, W q = w := by
      simp only [hW]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hsum]
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hWe : ∀ q, A *ᵥ W q = ((s q : ℝ) : ℂ) • (GQ *ᵥ W q) := by
      intro q
      have heig' : ∀ i, A *ᵥ (fun j => v.embedding (f i q j)) =
          ((s q : ℝ) : ℂ) • (GQ *ᵥ (fun j => v.embedding (f i q j))) := fun i => heig q _ (hf i q)
      rw [hW]
      simp only [Matrix.mulVec_sum, hmsm, heig', Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    have hsym : ∀ q r, ((s q : ℝ) : ℂ) * (star (W q) ⬝ᵥ GQ *ᵥ W r) =
        ((s r : ℝ) : ℂ) * (star (W q) ⬝ᵥ GQ *ᵥ W r) := by
      intro q r
      have e1 : star (W q) ⬝ᵥ A *ᵥ W r = ((s r : ℝ) : ℂ) * (star (W q) ⬝ᵥ GQ *ᵥ W r) := by
        rw [hWe r, hsm2]
      have e2 : star (W q) ⬝ᵥ A *ᵥ W r = ((s q : ℝ) : ℂ) * (star (W q) ⬝ᵥ GQ *ᵥ W r) := by
        rw [← hherm A hAH, hWe q, star_smul, hsm1, hherm GQ hGQH, hstar]
      exact e2.symm.trans e1
    have hterm : ∀ q r, (((s r : ℝ) : ℂ) - (smin : ℂ)) * (star (W q) ⬝ᵥ GQ *ᵥ W r) =
        ((Real.sqrt (s q - smin) : ℝ) : ℂ) * ((Real.sqrt (s r - smin) : ℝ) : ℂ) *
          (star (W q) ⬝ᵥ GQ *ᵥ W r) := by
      intro q r
      by_cases hqr : s q = s r
      · rw [hqr, ← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.2 (hs r)), Complex.ofReal_sub]
      · have hne : ((s q : ℝ) : ℂ) ≠ ((s r : ℝ) : ℂ) := by exact_mod_cast hqr
        have h0 : star (W q) ⬝ᵥ GQ *ᵥ W r = 0 := by
          have h := hsym q r
          have h' : (((s q : ℝ) : ℂ) - ((s r : ℝ) : ℂ)) * (star (W q) ⬝ᵥ GQ *ᵥ W r) = 0 := by
            rw [sub_mul, h, sub_self]
          rcases mul_eq_zero.mp h' with h'' | h''
          · exact absurd (sub_eq_zero.mp h'') hne
          · exact h''
        rw [h0, mul_zero, mul_zero]
    have hQw : star w ⬝ᵥ GQ *ᵥ w = ∑ q, ∑ r, star (W q) ⬝ᵥ GQ *ᵥ W r := by
      rw [← hWsum]
      simp only [star_sum, hsd, Matrix.mulVec_sum, hds]
    have hEw : star w ⬝ᵥ A *ᵥ w = ∑ q, ∑ r, ((s r : ℝ) : ℂ) * (star (W q) ⬝ᵥ GQ *ᵥ W r) := by
      rw [← hWsum]
      simp only [star_sum, hsd, Matrix.mulVec_sum, hds, hWe, hsm2]
    have hQz : star (∑ q, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • W q) ⬝ᵥ
        GQ *ᵥ (∑ q, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • W q) =
        ∑ q, ∑ r, ((Real.sqrt (s q - smin) : ℝ) : ℂ) * ((Real.sqrt (s r - smin) : ℝ) : ℂ) *
          (star (W q) ⬝ᵥ GQ *ᵥ W r) := by
      simp only [star_sum, hsd, Matrix.mulVec_sum, hds, star_smul, hsm1, hmsm, hsm2, hstar]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
      ring
    have hkey : star w ⬝ᵥ A *ᵥ w - (smin : ℂ) * (star w ⬝ᵥ GQ *ᵥ w) =
        star (∑ q, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • W q) ⬝ᵥ
          GQ *ᵥ (∑ q, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • W q) := by
      rw [hEw, hQw, hQz, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← hterm q r]
      ring
    rw [← hfQ, ← hfE, ← hfQ] at hkey
    have hreal : fnorm (XE v) (ι' *ᵥ w) ^ 2 - smin * fnorm (XQ v) w ^ 2 =
        fnorm (XQ v) (∑ q, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • W q) ^ 2 := by
      exact_mod_cast hkey
    nlinarith [sq_nonneg (fnorm (XQ v) (∑ q, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • W q))]
  rw [operator_norm_dual K a D Xa XE ha hE B v _ hc]
  intro x y
  obtain ⟨F, hF, hFn, -⟩ := quot_rep (H.map v.embedding) (X0 v) (h0 v).1 (h0 v).2
    (P.map v.embedding) (XQ v) (hQ v).1 (hQ v).2 (ι'⁻¹ *ᵥ y)
  have hy : ((ι * P).map v.embedding) *ᵥ F = y := by
    rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hF, ← hι'def, mul_inv_mulVec _ hι'U]
  have htr := pairC_transfer v B Pt (ι * P) col
    (fun φ F' => by rw [← Matrix.mulVec_mulVec]; exact hB φ F') x F
  rw [hy] at htr
  rw [htr]
  have h3 := (operator_norm_dual K b n Xb X0 hb (fun v => (h0 v).1) Pt v p hp0).mp hp
    ((col.map v.embedding) *ᵥ x) F
  have hop : ∀ {r t : ℕ} (M : Matrix (Fin t) (Fin r) ℂ) (u : Fin r → ℂ),
      Formalism.HermitianLatticesTheory.cnorm (M *ᵥ u) ≤ nrm M * Formalism.HermitianLatticesTheory.cnorm u := by
    intro r t M u
    rw [cnorm_eq, cnorm_eq u]
    unfold nrm
    have e : WithLp.toLp 2 (M *ᵥ u) =
        LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) (WithLp.toLp 2 u) := by
      simp [Matrix.toEuclideanLin_apply]
    rw [e]
    exact ContinuousLinearMap.le_opNorm _ _
  have h4 : fnorm (Xb v) ((col.map v.embedding) *ᵥ x) ≤ k * fnorm (Xa v) x := by
    have e : (Xb v)⁻¹ *ᵥ ((col.map v.embedding) *ᵥ x) =
        ((Xb v)⁻¹ * col.map v.embedding * Xa v) *ᵥ ((Xa v)⁻¹ *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_right _ _ (ha v)]
    have hnk : nrm ((Xb v)⁻¹ * col.map v.embedding * Xa v) ≤ k := by
      have := hk
      rwa [opNormAt_mulVecLin] at this
    show Formalism.HermitianLatticesTheory.cnorm ((Xb v)⁻¹ *ᵥ ((col.map v.embedding) *ᵥ x)) ≤
      k * Formalism.HermitianLatticesTheory.cnorm ((Xa v)⁻¹ *ᵥ x)
    rw [e]
    exact (hop _ _).trans (mul_le_mul_of_nonneg_right hnk (cnorm_nonneg _))
  have h5 : fnorm (X0 v) F ≤ fnorm (XE v) y / Real.sqrt smin := by
    rw [hFn]
    have hs1 := SPEC (ι'⁻¹ *ᵥ y)
    rw [mul_inv_mulVec _ hι'U] at hs1
    have hq0 : 0 ≤ fnorm (XQ v) (ι'⁻¹ *ᵥ y) := cnorm_nonneg _
    have he0 : 0 ≤ fnorm (XE v) y := cnorm_nonneg _
    have h6 : (fnorm (XQ v) (ι'⁻¹ *ᵥ y) * Real.sqrt smin) ^ 2 ≤ fnorm (XE v) y ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hsmin.le]
      linarith
    have h7 : fnorm (XQ v) (ι'⁻¹ *ᵥ y) * Real.sqrt smin ≤ fnorm (XE v) y := by
      have := Real.sqrt_le_sqrt h6
      rwa [Real.sqrt_sq (mul_nonneg hq0 hr.le), Real.sqrt_sq he0] at this
    first
      | exact (le_div_iff₀ hr).mpr h7
      | exact (le_div_iff hr).mpr h7
  calc ‖pairC v Pt ((col.map v.embedding) *ᵥ x) F‖
      ≤ p * fnorm (Xb v) ((col.map v.embedding) *ᵥ x) * fnorm (X0 v) F := h3
    _ ≤ p * (k * fnorm (Xa v) x) * (fnorm (XE v) y / Real.sqrt smin) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h4 hp0) h5 (cnorm_nonneg _)
          (mul_nonneg hp0 (mul_nonneg hk0 (cnorm_nonneg _)))
    _ = p * k / Real.sqrt smin * fnorm (Xa v) x * fnorm (XE v) y := by ring

end OperatorNormFrames

open OperatorNormFrames in
theorem height_constant_first : HeightBoundConstant := by
  unfold HeightBoundConstant
  intro K _ _ _ n D m c Xc hXc Kj H X0 h0 P hP XQ hQ XE hE ι hι Ix J _ _ _ Qp hsup κ lam lamL
    hκ hlamL hle hspec Pt B hB hB0 pU kU hpU hkU
  have hcomp := composition_norm_at_place K m c Xc hXc Kj
  have hk : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤ ∏ j, kU j v := fun v =>
    (hcomp.1 v).trans (Finset.prod_le_prod (fun j _ => opNormAt_nonneg _ _ _ _ _ _)
      (fun j _ => hkU j v))
  have hBpos : ∀ v, 0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B := by
    intro v
    rw [opNormAt_dual_eq (Xc 0) XE hE B v, norm_pos_iff]
    intro h0'
    apply hB0
    have hM := Matrix.toEuclideanLin.map_eq_zero_iff.mp
      (LinearMap.toContinuousLinearMap.map_eq_zero_iff.mp h0')
    have hTu : IsUnit ((XE v)ᵀ).det := by
      rw [Matrix.det_transpose]
      exact hE v
    have hP0 : pmat v B = 0 := by
      have := congrArg (fun M => ((XE v)ᵀ)⁻¹ * M * (Xc 0 v)⁻¹) hM
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hTu,
        Matrix.mul_nonsing_inv _ (hXc 0 v), Matrix.mul_one, Matrix.mul_zero,
        Matrix.zero_mul] at this
      exact this
    have hentry : ∀ i k, B (Pi.single i 1) (Pi.single k 1) = 0 := by
      intro i k
      have := congrFun (congrFun hP0 k) i
      simpa [pmat] using this
    refine LinearMap.ext fun φ => LinearMap.ext fun e' => ?_
    have hd : ∀ i, B (Pi.single i 1) e' = 0 := by
      intro i
      rw [dual_expand (B (Pi.single i 1)) e']
      simp [hentry]
    rw [map_expand B φ e']
    simp [hd]
  have hlogv : ∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2) ≤
      Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) - Real.log (κ v) -
        minOver (fun p => ∑ j, Real.log (lamL j p v)) := by
    intro v
    have S1 : 0 < κ v * minOver (fun p => ∏ j, lamL j p v) :=
      (successive_minimum_log Ix J (κ v) (fun j p => lamL j p v) (hκ v) fun j p => hlamL j p v).1
    have S2 : ∀ p, κ v * minOver (fun p => ∏ j, lamL j p v) ≤ κ v * ∏ j, lamL j p v :=
      (successive_minimum_log Ix J (κ v) (fun j p => lamL j p v) (hκ v) fun j p => hlamL j p v).2.1
    have S4 : Real.log (κ v * minOver (fun p => ∏ j, lamL j p v)) =
        Real.log (κ v) + minOver (fun p => ∑ j, Real.log (lamL j p v)) :=
      (successive_minimum_log Ix J (κ v) (fun j p => lamL j p v) (hκ v) fun j p => hlamL j p v).2.2.2
    have hs : ∀ p, κ v * minOver (fun p => ∏ j, lamL j p v) ≤ κ v * ∏ j, lam j p v := fun p =>
      (S2 p).trans (mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun j _ => (hlamL j p v).le) (fun j _ => hle j p v)) (hκ v).le)
    have hpl := place_bound (Xc 0) (hXc 0) (Xc (Fin.last m)) (hXc (Fin.last m))
      (chainMat Kj (Fin.last m)) H X0 h0 P hP XQ hQ XE hE ι hι Qp hsup v
      (fun p => κ v * ∏ j, lam j p v) (κ v * minOver (fun p => ∏ j, lamL j p v)) S1 hs
      (fun p x hx y => hspec v p x hx y) Pt B hB (pU v) (∏ j, kU j v) (hpU v) (hk v)
    have hpos := hBpos v
    have hpUnn : 0 ≤ pU v := (opNormAt_nonneg _ _ _ _ _ _).trans (hpU v)
    have hkUnn : ∀ j, 0 ≤ kU j v := fun j => (opNormAt_nonneg _ _ _ _ _ _).trans (hkU j v)
    have hsq : 0 < Real.sqrt (κ v * minOver (fun p => ∏ j, lamL j p v)) := Real.sqrt_pos.2 S1
    have hnum : 0 < pU v * ∏ j, kU j v :=
      (div_pos_iff_of_pos_right hsq).mp (hpos.trans_le hpl)
    have hprod : 0 < ∏ j, kU j v := by
      first
        | exact pos_of_mul_pos_right hnum hpUnn
        | nlinarith [Finset.prod_nonneg fun j (_ : j ∈ Finset.univ) => hkUnn j]
    have hpUpos : 0 < pU v := by
      rcases lt_or_eq_of_le hpUnn with h | h
      · exact h
      · rw [← h, zero_mul] at hnum
        exact absurd hnum (lt_irrefl _)
    have hkUpos : ∀ j, 0 < kU j v := by
      intro j
      rcases lt_or_eq_of_le (hkUnn j) with h | h
      · exact h
      · have : ∏ j, kU j v = 0 := Finset.prod_eq_zero (Finset.mem_univ j) h.symm
        rw [this] at hprod
        exact absurd hprod (lt_irrefl _)
    have hlogprod : ∑ j, Real.log (kU j v ^ 2) = Real.log (∏ j, kU j v ^ 2) := by
      symm
      first
        | exact Real.log_prod fun j _ => (pow_pos (hkUpos j) 2).ne'
        | exact Real.log_prod _ _ fun j _ => (pow_pos (hkUpos j) 2).ne'
    calc Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
          (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2)
        ≤ Real.log (pU v ^ 2 * (∏ j, kU j v ^ 2) / (κ v * minOver (fun p => ∏ j, lamL j p v))) := by
          apply Real.log_le_log (pow_pos hpos 2)
          have e : pU v ^ 2 * (∏ j, kU j v ^ 2) / (κ v * minOver (fun p => ∏ j, lamL j p v)) =
              (pU v * (∏ j, kU j v) / Real.sqrt (κ v * minOver (fun p => ∏ j, lamL j p v))) ^ 2 := by
            rw [div_pow, mul_pow, Real.sq_sqrt S1.le, Finset.prod_pow]
          rw [e]
          have := hpos.le
          gcongr
      _ = Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) -
            Real.log (κ v * minOver (fun p => ∏ j, lamL j p v)) := by
          rw [Real.log_div (mul_pos (pow_pos hpUpos 2)
              (Finset.prod_pos fun j _ => pow_pos (hkUpos j) 2)).ne' S1.ne',
            Real.log_mul (pow_pos hpUpos 2).ne' (Finset.prod_pos fun j _ => pow_pos (hkUpos j) 2).ne',
            ← hlogprod]
      _ = Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) - Real.log (κ v) -
            minOver (fun p => ∑ j, Real.log (lamL j p v)) := by
          rw [S4]
          ring
  refine ⟨hlogv, ?_⟩
  unfold Formalism.HN.htMap meanLog
  calc (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
        (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2)
      ≤ (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, (Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) -
          Real.log (κ v) - minOver (fun p => ∑ j, Real.log (lamL j p v))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hlogv v) (by positivity)
    _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        ring

end Formalism.DivisionValues
