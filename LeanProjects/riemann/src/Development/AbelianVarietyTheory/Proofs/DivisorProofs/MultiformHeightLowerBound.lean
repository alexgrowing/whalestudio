import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffLeOfBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFrameNormEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogEvalSubLeBlockSphereMeanMultidegreeStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HtLowProof

theorem eval_blockScale_multi {B N : ℕ} {a : Fin B → ℕ} {h : MvPolynomial (Fin B × Fin N) ℂ}
    (hh : IsMultiHomogeneous a h) (r : Fin B → ℂ) (v : Fin B × Fin N → ℂ) :
    eval (fun q => r q.1 * v q) h = (∏ i, r i ^ a i) * eval v h := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hr : ∏ q : Fin B × Fin N, r q.1 ^ s q = ∏ i, r i ^ a i := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    show ∏ y, r i ^ s (i, y) = _
    rw [Finset.prod_pow_eq_pow_sum, hh s hs i]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hr]
  ring

theorem frameNorm_sum_le {N n : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : Fin n → ℂ) (u : Fin n → Fin N → ℂ)
    (Λ : ℝ) (hc : ∀ k, ‖c k‖ ≤ 1) (hu : ∀ k, frameNorm A (u k) ≤ Λ) :
    frameNorm A (∑ k, c k • u k) ≤ n * Λ := by
  let T : (Fin N → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm.toLinearMap ∘ₗ A⁻¹.mulVecLin
  have hT : ∀ z, frameNorm A z = ‖T z‖ := fun z => by
    rw [frameNorm, EuclideanSpace.norm_eq]; rfl
  rw [hT, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _k : Fin n, Λ := Finset.sum_le_sum fun k _ => by
        rw [map_smul, norm_smul, ← hT]
        exact (mul_le_of_le_one_left (GlobalTheory.MaxPoint.frameNorm_nonneg' _ _) (hc k)).trans (hu k)
    _ = n * Λ := by simp

theorem norm_eval_le {B N : ℕ} {a : Fin B → ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) (hN : 0 < N)
    {h : MvPolynomial (Fin B × Fin N) ℂ} (hh : IsMultiHomogeneous a h) (R : ℝ) (hR : 0 ≤ R)
    (u : Fin B × Fin N → ℂ) (hu : ∀ i, frameNorm A (fun j => u (i, j)) ≤ R) :
    ‖eval u h‖ ≤ Real.exp (blockSphereMean B N (linSubst A h) + (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2) *
      R ^ (∑ i, a i) := by
  set r : Fin B → ℝ := fun i => frameNorm A (fun j => u (i, j)) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => GlobalTheory.MaxPoint.frameNorm_nonneg' _ _
  set e : Fin N → ℂ := A.mulVec (Pi.single ⟨0, hN⟩ 1) with he'
  have he : frameNorm A e = 1 := by
    rw [he', GlobalTheory.MaxPoint.frameNorm_mulVec hA]
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N) (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
    simp
  let p : Fin B × Fin N → ℂ := fun q => if r q.1 = 0 then e q.2 else ((r q.1)⁻¹ : ℂ) * u q
  have hp : ∀ i, frameNorm A (fun j => p (i, j)) = 1 := fun i => by
    by_cases h0 : r i = 0
    · have : (fun j => p (i, j)) = e := by funext j; simp [p, h0]
      rw [this, he]
    · have : (fun j => p (i, j)) = ((r i)⁻¹ : ℂ) • (fun j => u (i, j)) := by
        funext j; simp [p, h0]
      rw [this, GlobalTheory.MaxPoint.frameNorm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hr0 i)]
      exact inv_mul_cancel₀ h0
  have hup : u = fun q => ((r q.1 : ℝ) : ℂ) * p q := by
    funext q
    by_cases h0 : r q.1 = 0
    · have hz : (fun j => u (q.1, j)) = 0 := GlobalTheory.MaxPoint.eq_zero_of_frameNorm_eq_zero hA h0
      have := congrFun hz q.2
      simp only [Pi.zero_apply] at this
      simp [h0, this]
    · simp only [p, if_neg h0]
      rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ h0, Complex.ofReal_one, one_mul]
  have hval : ‖eval u h‖ = (∏ i, r i ^ a i) * ‖eval p h‖ := by
    rw [hup, eval_blockScale_multi hh (fun i => ((r i : ℝ) : ℂ)) p, norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (hr0 i)]
  have hprod : ∏ i, r i ^ a i ≤ R ^ (∑ i, a i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun i _ => pow_nonneg (hr0 i) _) fun i _ => pow_le_pow_left₀ (hr0 i) (hu i) _
  rw [hval]
  by_cases hz : eval p h = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hR _)
  · have harch := GlobalTheory.T.log_eval_sub_le_blockSphereMean_multidegree B N a A h hA hh p hp hz
    have hle : ‖eval p h‖ ≤ Real.exp (blockSphereMean B N (linSubst A h) +
        (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 hz)]
      exact Real.exp_le_exp.2 (by linarith)
    rw [mul_comm]
    exact mul_le_mul hle hprod (Finset.prod_nonneg fun i _ => pow_nonneg (hr0 i) _) (Real.exp_pos _).le

theorem eval₂_linSubst {F : Type} [Field F] {B N n : ℕ} (s : F →+* ℂ) (w : Matrix (Fin N) (Fin n) F)
    (G : MvPolynomial (Fin B × Fin N) F) (z : Fin B × Fin n → ℂ) :
    eval₂ s z (linSubst w G) = eval (fun q => ∑ k, z (q.1, k) * s (w q.2 k)) (MvPolynomial.map s G) := by
  have e : ((eval₂Hom s z).comp (aeval (fun p : Fin B × Fin N => ∑ k, C (w p.2 k) * X (p.1, k)) :
      MvPolynomial (Fin B × Fin N) F →ₐ[F] MvPolynomial (Fin B × Fin n) F).toRingHom) =
      (eval (fun q => ∑ k, z (q.1, k) * s (w q.2 k))).comp (MvPolynomial.map s) := by
    refine MvPolynomial.ringHom_ext (fun c => by simp) (fun q => ?_)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, map_sum, map_mul,
      coe_eval₂Hom, eval₂_C, eval₂_X, map_X, eval_X]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  exact RingHom.congr_fun e G

theorem htLow : HtLow := by
  intro F _ _ B N n w A Λ hL a G hG ha
  obtain ⟨P, hP⟩ := GlobalTheory.HeightUnique.exists_right_inv hL.spans
  have hk : linSubst w G ≠ 0 := GlobalTheory.HeightUnique.linSubst_ne_zero hP hG
  have hNn : N ≤ n := by
    have h1 := finrank_range_le_card (R := F) w.col
    unfold Set.finrank at h1
    rw [hL.spans, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (hL.pos.trans_le hNn)
  have hnΛ : (0 : ℝ) < n * Λ := mul_pos (by linarith) (by linarith [hL.one_le])
  set deg : ℝ := ∑ b, (a b : ℝ) with hdeg
  set H : ℝ := (harmonic (N - 1) : ℝ) with hH
  set m : (F →+* ℂ) → ℝ := fun σ => blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ G)) with hm
  have key := GlobalTheory.HSFloor.floor F (Fin B × Fin n) (linSubst w G)
    (fun s => Real.exp (m s + deg * H / 2) * ((n : ℝ) * Λ) ^ (∑ b, a b)) hk (fun s z hz => by
      rw [eval₂_linSubst]
      refine norm_eval_le (hL.det s) hL.pos (isMultiHomogeneous_map_ring a G ha s) _ hnΛ.le _ fun i => ?_
      have e : (fun j => ∑ k, z (i, k) * s (w j k)) = ∑ k, z (i, k) • (fun j => s (w j k)) := by
        funext j; simp [Finset.sum_apply]
      rw [e]
      exact frameNorm_sum_le _ _ _ Λ (fun k => hz _) fun k => hL.le k s)
  have hd : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.2 Module.finrank_pos
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) = Module.finrank ℚ F := by
    rw [NumberField.Embeddings.card]
  have hlog : ∀ s, Real.log (Real.exp (m s + deg * H / 2) * ((n : ℝ) * Λ) ^ (∑ b, a b)) =
      m s + (deg * H / 2 + deg * Real.log (n * Λ)) := fun s => by
    rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hnΛ _).ne', Real.log_exp, Real.log_pow, hdeg]
    push_cast
    ring
  have hmean : mean F (fun s => Real.log (Real.exp (m s + deg * H / 2) * ((n : ℝ) * Λ) ^ (∑ b, a b))) =
      mean F m + (deg * H / 2 + deg * Real.log (n * Λ)) := by
    simp only [hlog, mean, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
  have hht : ht w A G = finPart (linSubst w G) + mean F m := by
    simp only [ht, formHeight, finPart, mean, hm]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
    rw [add_div]
  have hHle : H ≤ Real.log n + 1 := by
    have h1 : H ≤ 1 + Real.log ((N - 1 : ℕ) : ℝ) := by
      rw [hH]; exact_mod_cast harmonic_le_one_add_log (N - 1)
    have h2 : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log n := by
      rcases Nat.eq_zero_or_pos (N - 1) with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg hn1
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (by omega : N - 1 ≤ n))
    linarith
  have hdeg0 : 0 ≤ deg := Finset.sum_nonneg fun b _ => Nat.cast_nonneg _
  rw [hmean] at key
  rw [hht, cst]
  nlinarith [mul_le_mul_of_nonneg_left hHle hdeg0]

end GlobalTheory.HtLowProof
