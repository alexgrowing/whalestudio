import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelOfRiemann
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodsSubframeDetBounds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAndCuspWeightBoundsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SymplecticPolydiscPeriodBasis
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPuncturedExpOrder
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PLogCoverDescent
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.ULog

theorem quad_re {g : ℕ} (M : Matrix (Fin g) (Fin g) ℝ) (α y : Fin g → ℝ) :
    (((fun k => (α k : ℂ) + (y k : ℂ) * Complex.I) ⬝ᵥ (M.map Complex.ofReal) *ᵥ
      star (fun k => (α k : ℂ) + (y k : ℂ) * Complex.I))).re =
      α ⬝ᵥ M *ᵥ α + y ⬝ᵥ M *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re, Complex.mul_im]

theorem quad_vecMul {g : ℕ} (x : Fin g → ℂ) (A H : Matrix (Fin g) (Fin g) ℂ) :
    (x ᵥ* A) ⬝ᵥ H *ᵥ star (x ᵥ* A) = x ⬝ᵥ (A * H * Aᴴ) *ᵥ star x := by
  rw [star_vecMul, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec,
    Matrix.mul_assoc]

theorem inv_quad_lower {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) {t : ℝ} (ht : 0 < t)
    (hle : (t • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef) (α : Fin g → ℝ) :
    t⁻¹ * (α ⬝ᵥ α) ≤ α ⬝ᵥ Y⁻¹ *ᵥ α := by
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hY.isUnit
  have hYs : Yᵀ = Y := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hY.isHermitian
  obtain ⟨u, hu_def⟩ : ∃ u, u = Y⁻¹ *ᵥ α := ⟨_, rfl⟩
  have hYu : Y *ᵥ u = α := by
    rw [hu_def, mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, one_mulVec]
  have hsw : ∀ p q : Fin g → ℝ, p ⬝ᵥ Y *ᵥ q = q ⬝ᵥ Y *ᵥ p := by
    intro p q
    rw [dotProduct_mulVec, ← mulVec_transpose, hYs, dotProduct_comm]
  have h1 : 0 ≤ (u - t⁻¹ • α) ⬝ᵥ Y *ᵥ (u - t⁻¹ • α) := by
    have := hY.posSemidef.dotProduct_mulVec_nonneg (u - t⁻¹ • α)
    simpa using this
  have h2 : 0 ≤ α ⬝ᵥ (t • (1 : Matrix (Fin g) (Fin g) ℝ) - Y) *ᵥ α := by
    have := hle.dotProduct_mulVec_nonneg α
    simpa using this
  have e2 : α ⬝ᵥ (t • (1 : Matrix (Fin g) (Fin g) ℝ) - Y) *ᵥ α = t * (α ⬝ᵥ α) - α ⬝ᵥ Y *ᵥ α := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have e3 : u ⬝ᵥ Y *ᵥ α = α ⬝ᵥ α := by rw [hsw, hYu]
  have e1 : (u - t⁻¹ • α) ⬝ᵥ Y *ᵥ (u - t⁻¹ • α) =
      u ⬝ᵥ α - 2 * t⁻¹ * (α ⬝ᵥ α) + t⁻¹ ^ 2 * (α ⬝ᵥ Y *ᵥ α) := by
    rw [mulVec_sub, mulVec_smul, hYu, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, e3]
    simp only [smul_eq_mul]
    ring
  have e4 : u ⬝ᵥ α = α ⬝ᵥ Y⁻¹ *ᵥ α := by rw [hu_def, dotProduct_comm]
  rw [← e4]
  rw [e1] at h1
  rw [e2] at h2
  have ht' : 0 < t⁻¹ := inv_pos.2 ht
  have h3 : t⁻¹ ^ 2 * (α ⬝ᵥ Y *ᵥ α) ≤ t⁻¹ * (α ⬝ᵥ α) := by
    have : t⁻¹ ^ 2 * (α ⬝ᵥ Y *ᵥ α) ≤ t⁻¹ ^ 2 * (t * (α ⬝ᵥ α)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    refine this.trans (le_of_eq ?_)
    field_simp
  linarith

theorem int_sq_ge {g : ℕ} {v : Fin g → ℤ} (hv : v ≠ 0) :
    1 ≤ (fun k => (v k : ℝ)) ⬝ᵥ (fun k => (v k : ℝ)) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  have h1 : (1 : ℝ) ≤ (v j : ℝ) * (v j : ℝ) := by
    have : (1 : ℤ) ≤ v j * v j := by
      have h : v j ≠ 0 := by simpa using hj
      have := Int.one_le_abs h
      nlinarith [abs_mul_abs_self (v j), abs_nonneg (v j)]
    exact_mod_cast this
  refine h1.trans ?_
  simp only [dotProduct]
  exact Finset.single_le_sum (f := fun k => (v k : ℝ) * (v k : ℝ))
    (fun i _ => mul_self_nonneg _) (Finset.mem_univ j)

theorem real_lower {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) {c t : ℝ} (ht : 0 < t)
    (hc : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) (hc0 : 0 < c)
    (hle : (t • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef)
    (X : Matrix (Fin g) (Fin g) ℝ) (a n : Fin g → ℤ) (hne : a ≠ 0 ∨ n ≠ 0) :
    min c t⁻¹ ≤
      (((fun k => (a k : ℝ)) + (fun k => (n k : ℝ)) ᵥ* X) ⬝ᵥ Y⁻¹ *ᵥ
        ((fun k => (a k : ℝ)) + (fun k => (n k : ℝ)) ᵥ* X)) +
      ((fun k => (n k : ℝ)) ᵥ* Y) ⬝ᵥ Y⁻¹ *ᵥ ((fun k => (n k : ℝ)) ᵥ* Y) := by
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hY.isUnit
  have hYs : Yᵀ = Y := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hY.isHermitian
  have hinv : (Y⁻¹).PosSemidef := hY.inv.posSemidef
  have hq : ∀ p : Fin g → ℝ, 0 ≤ p ⬝ᵥ Y⁻¹ *ᵥ p := by
    intro p
    have := hinv.dotProduct_mulVec_nonneg p
    simpa using this
  by_cases hn : n = 0
  · have ha : a ≠ 0 := by
      rcases hne with h | h
      · exact h
      · exact absurd hn h
    subst hn
    have h0 : (fun k => (((0 : Fin g → ℤ) k : ℤ) : ℝ)) = 0 := by
      funext k
      simp
    rw [h0, zero_vecMul, zero_vecMul, add_zero]
    have h1 := inv_quad_lower hY ht hle (fun k => (a k : ℝ))
    have h2 := int_sq_ge ha
    have ht' : 0 < t⁻¹ := inv_pos.2 ht
    have h3 : t⁻¹ ≤ t⁻¹ * ((fun k => (a k : ℝ)) ⬝ᵥ (fun k => (a k : ℝ))) :=
      le_mul_of_one_le_right ht'.le h2
    simp only [dotProduct_zero, mulVec_zero, add_zero]
    exact (min_le_right _ _).trans (h3.trans h1)
  · obtain ⟨N, hN⟩ : ∃ N : Fin g → ℝ, N = fun k => (n k : ℝ) := ⟨_, rfl⟩
    have e1 : N ᵥ* Y = Y *ᵥ N := by
      rw [← mulVec_transpose, hYs]
    have e2 : Y⁻¹ *ᵥ (Y *ᵥ N) = N := by
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, one_mulVec]
    have h1 : 0 ≤ N ⬝ᵥ (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)) *ᵥ N := by
      have := hc.dotProduct_mulVec_nonneg N
      simpa using this
    have e3 : N ⬝ᵥ (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)) *ᵥ N = N ⬝ᵥ Y *ᵥ N - c * (N ⬝ᵥ N) := by
      rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have h2 : 1 ≤ N ⬝ᵥ N := by
      rw [hN]
      exact int_sq_ge hn
    rw [← hN, e1, e2, dotProduct_comm (Y *ᵥ N) N]
    rw [e3] at h1
    have h3 := hq ((fun k => (a k : ℝ)) + N ᵥ* X)
    have h4 : c ≤ c * (N ⬝ᵥ N) := le_mul_of_one_le_right hc0.le h2
    have h5 := min_le_left c t⁻¹
    rw [← hN] at *
    linarith

theorem final_num {c t K S V : ℝ} (hc : 0 < c) (ht : 0 < t) (hS : 1 ≤ S) (hK1 : c⁻¹ ≤ K)
    (hK2 : t ≤ K * S) (hV : min c t⁻¹ ≤ V) : 1 ≤ K * S * V := by
  have hK0 : 0 < K := lt_of_lt_of_le (inv_pos.2 hc) hK1
  have hKS : 0 < K * S := mul_pos hK0 (by linarith)
  have h1 : (K * S)⁻¹ ≤ min c t⁻¹ := by
    refine le_min ?_ ?_
    · rw [inv_le_comm₀ hKS hc]
      exact hK1.trans (le_mul_of_one_le_right hK0.le hS)
    · exact inv_anti₀ ht hK2
  have h2 : (K * S)⁻¹ ≤ V := h1.trans hV
  calc (1 : ℝ) = K * S * (K * S)⁻¹ := (mul_inv_cancel₀ hKS.ne').symm
    _ ≤ K * S * V := mul_le_mul_of_nonneg_left h2 hKS.le

theorem lattice_lower {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 1 ≤ K ∧ ∀ w ∈ logCover L.a_le, ‖expCover a w‖ < ρ → ∀ v : Λ, v ≠ 0 →
      1 ≤ K * Flat.logSize a (expCover a w) *
        (L.P w v ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w v)).re := by
  obtain ⟨bas, Q, A, T0, hsym, hAd, hdet, -, -, hAP, hQP⟩ :=
    Flat.exists_markedPeriods_frame n a g Λ L
  obtain ⟨ρ₁, c, C, hρ₁, hρ₁1, hc, hb⟩ :=
    (ImTauBounds.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof)
      n a g Q
  have hC' : 0 < |C| + 1 := by positivity
  have he : 0 < Real.exp 1 + 2 := by positivity
  refine ⟨ρ₁, c⁻¹ + (|C| + 1) * (Real.exp 1 + 2) + 1, hρ₁, ?_, ?_⟩
  · have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < (|C| + 1) * (Real.exp 1 + 2) := by positivity
    linarith
  intro w hw hzρ v hv
  obtain ⟨z, hzdef⟩ : ∃ z, z = expCover a w := ⟨_, rfl⟩
  rw [← hzdef] at hzρ ⊢
  have hz1 : ∀ k, ‖z k‖ < 1 := fun k =>
    lt_of_le_of_lt (norm_le_pi_norm z k) (hzρ.trans hρ₁1)
  have h0 : ∀ i : Fin n, i.val < a → z i ≠ 0 := by
    intro i hi
    rw [hzdef]
    simp [expCover, hi, Complex.exp_ne_zero]
  have hzc : expCover a w ∈ Metric.closedBall (0 : Fin n → ℂ) ρ₁ := by
    rw [← hzdef]
    simpa [dist_zero_right] using hzρ.le
  obtain ⟨hb1, hb2⟩ := hb w hw hzc
  rw [← hzdef] at hb2
  obtain ⟨hr1, hr2⟩ := Flat.chartRadius_le_log_sum L.a_le z hz1 h0
  obtain ⟨r, hr⟩ : ∃ r, r = GroundTheory.Heights₂.Heights.chartRadius L.a_le z := ⟨_, rfl⟩
  rw [← hr] at hr1 hr2 hb2
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = (Q.τ w).map Complex.im := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X, X = (Q.τ w).map Complex.re := ⟨_, rfl⟩
  rw [← hYdef] at hb1 hb2
  have hYp : Y.PosDef := hYdef ▸ Q.im_posDef w hw
  have ht : 0 < (|C| + 1) * r := mul_pos hC' (by linarith)
  have hle : (((|C| + 1) * r) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef := by
    have h1 : ((((|C| + 1) - C) * r) • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef := by
      refine Matrix.PosSemidef.one.smul ?_
      have : 0 ≤ (|C| + 1) - C := by linarith [le_abs_self C]
      exact mul_nonneg this (by linarith)
    have h2 := hb2.add h1
    have e : (C * r) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y +
        ((|C| + 1 - C) * r) • (1 : Matrix (Fin g) (Fin g) ℝ) =
        ((|C| + 1) * r) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y := by
      module
    rwa [e] at h2

  let Am : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i => L.P w (bas (.inl i))
  let Bm : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i => L.P w (bas (.inr i))
  obtain ⟨h1, -, -, h4⟩ := Flat.siegel_of_riemann g Am Bm (L.H (expCover a w)) (L.herm w hw)
    (L.pos w hw) (fun i j => ⟨(L.im w hw (bas (.inl i)) (bas (.inl j))).trans (by simp [(hsym i j).1]),
      (L.im w hw (bas (.inr i)) (bas (.inr j))).trans (by simp [(hsym i j).2.1]),
      (L.im w hw (bas (.inl i)) (bas (.inr j))).trans (by
        rw [(hsym i j).2.2]; split_ifs <;> simp)⟩)
  have hB : Bm = Q.τ w * Am := by
    ext j k
    have h := congrFun (hQP w hw j) k
    rw [Finset.sum_apply] at h
    simpa [Am, Bm, Matrix.mul_apply] using h
  have hτ : Bm * Am⁻¹ = Q.τ w := by
    rw [hB, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h1), Matrix.mul_one]
  rw [hτ, ← hYdef] at h4

  obtain ⟨av, hav⟩ : ∃ av : Fin g → ℤ, av = fun i => bas.repr v (.inl i) := ⟨_, rfl⟩
  obtain ⟨nv, hnv⟩ : ∃ nv : Fin g → ℤ, nv = fun i => bas.repr v (.inr i) := ⟨_, rfl⟩
  have hne : av ≠ 0 ∨ nv ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hv
    have : bas.repr v = 0 := by
      ext x
      rcases x with i | i
      · exact congrFun (hav.symm.trans hcon.1) i
      · exact congrFun (hnv.symm.trans hcon.2) i
    simpa using this
  have hvs : v = ∑ i, av i • bas (.inl i) + ∑ j, nv j • bas (.inr j) := by
    have := (bas.sum_repr v).symm
    rw [Fintype.sum_sum_type] at this
    rw [hav, hnv]
    exact this
  obtain ⟨x, hx⟩ : ∃ x : Fin g → ℂ, x = fun k => ((av k : ℝ) + ((fun j => (nv j : ℝ)) ᵥ* X) k : ℝ) +
      (((fun j => (nv j : ℝ)) ᵥ* Y) k : ℝ) * Complex.I := ⟨_, rfl⟩
  have hPv : L.P w v = x ᵥ* Am := by
    have hx' : ∀ k, x k = (av k : ℂ) + ∑ j, (nv j : ℂ) * Q.τ w j k := by
      intro k
      rw [hx]
      apply Complex.ext
      · simp [vecMul, dotProduct, hXdef, hYdef, Complex.re_sum]
      · simp [vecMul, dotProduct, hXdef, hYdef, Complex.im_sum]
    have hf : ∀ j, L.P w (bas (.inr j)) = Q.τ w j ᵥ* Am := by
      intro j
      rw [hQP w hw j]
      ext k
      simp [vecMul, dotProduct, Am, Finset.sum_apply]
    rw [hvs]
    simp only [map_add, map_sum, map_zsmul, hf]
    ext k
    have e1 : (∑ i, av i • L.P w (bas (.inl i))) k = ∑ i, (av i : ℂ) * Am i k := by
      simp [Finset.sum_apply, Am]
    have e2 : (∑ j, nv j • (Q.τ w j ᵥ* Am)) k = ∑ j, (nv j : ℂ) * ∑ i, Q.τ w j i * Am i k := by
      simp [Finset.sum_apply, vecMul, dotProduct]
    rw [Pi.add_apply, e1, e2]
    simp only [vecMul, dotProduct, hx', add_mul, Finset.sum_add_distrib, Finset.sum_mul,
      Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hV := real_lower hYp ht (hYdef ▸ hb1) hc hle X av nv hne
  have hq := quad_re (Y⁻¹) ((fun k => (av k : ℝ)) + (fun j => (nv j : ℝ)) ᵥ* X)
    ((fun j => (nv j : ℝ)) ᵥ* Y)
  have hval : (L.P w v ⬝ᵥ L.H z *ᵥ star (L.P w v)).re =
      (((fun k => (av k : ℝ)) + (fun k => (nv k : ℝ)) ᵥ* X) ⬝ᵥ Y⁻¹ *ᵥ
        ((fun k => (av k : ℝ)) + (fun k => (nv k : ℝ)) ᵥ* X)) +
      ((fun k => (nv k : ℝ)) ᵥ* Y) ⬝ᵥ Y⁻¹ *ᵥ ((fun k => (nv k : ℝ)) ᵥ* Y) := by
    rw [hPv, quad_vecMul, hzdef, h4, hx]
    exact hq
  rw [hval]
  have hS : 1 ≤ Flat.logSize a z := by
    have : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    simp only [Flat.logSize]
    linarith
  refine final_num hc ht hS ?_ ?_ hV
  · have : 0 < (|C| + 1) * (Real.exp 1 + 2) := by positivity
    linarith
  · have hr3 : r ≤ (Real.exp 1 + 2) * Flat.logSize a z := hr2
    have h5 : 0 < c⁻¹ := inv_pos.2 hc
    have h6 : (|C| + 1) * r ≤ (|C| + 1) * ((Real.exp 1 + 2) * Flat.logSize a z) :=
      mul_le_mul_of_nonneg_left hr3 hC'.le
    have h7 : (c⁻¹ + 1) * Flat.logSize a z ≥ 0 := by
      have : (0 : ℝ) ≤ Flat.logSize a z := by linarith
      positivity
    nlinarith

theorem first_minimum_sq_lower_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] [Nontrivial Λ] (R : RiemLat E g Λ) {T : ℝ} (hT : 0 < T)
    (h : ∀ v : Λ, v ≠ 0 → 1 ≤ T * R.normSq v) : 0 < R.lam1 ∧ 1 ≤ T * R.lam1 ^ 2 := by
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : Λ)
  have hlow : Real.sqrt T⁻¹ ≤ R.lam1 := by
    refine le_csInf ⟨_, v₀, hv₀, rfl⟩ ?_
    rintro x ⟨v, hv, rfl⟩
    refine Real.sqrt_le_sqrt ?_
    rw [inv_le_iff_one_le_mul₀ hT, mul_comm]
    exact h v hv
  have hs : 0 < Real.sqrt T⁻¹ := Real.sqrt_pos.2 (inv_pos.2 hT)
  have hpos : 0 < R.lam1 := lt_of_lt_of_le hs hlow
  refine ⟨hpos, ?_⟩
  have h2 : T⁻¹ ≤ R.lam1 ^ 2 := by
    have := pow_le_pow_left₀ hs.le hlow 2
    rwa [Real.sq_sqrt (inv_pos.2 hT).le] at this
  calc (1 : ℝ) = T * T⁻¹ := (mul_inv_cancel₀ hT.ne').symm
    _ ≤ T * R.lam1 ^ 2 := mul_le_mul_of_nonneg_left h2 hT.le

theorem two_log_le {K S l : ℝ} (hK : 1 ≤ K) (hS : 1 ≤ S) (hl : 0 < l) (h : 1 ≤ K * S * l ^ 2) :
    2 * max 0 (Real.log (1 / l)) ≤ Real.log K + Real.log S := by
  have hK0 : 0 < K := by linarith
  have hS0 : 0 < S := by linarith
  have h1 : 0 ≤ Real.log K := Real.log_nonneg hK
  have h2 : 0 ≤ Real.log S := Real.log_nonneg hS
  have h3 : 2 * Real.log (1 / l) ≤ Real.log K + Real.log S := by
    have e : 2 * Real.log (1 / l) = Real.log ((1 / l) ^ 2) := by
      rw [Real.log_pow]
      norm_num
    rw [e, ← Real.log_mul hK0.ne' hS0.ne']
    refine Real.log_le_log (by positivity) ?_
    rw [one_div, inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
    linarith
  rcases max_cases 0 (Real.log (1 / l)) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith

theorem abs_log_le {K S d : ℝ} {N : ℕ} (hS : 1 ≤ S) (hd : d ≤ K) (hd2 : 1 ≤ K * S ^ N * d)
    (hK : 1 ≤ K) : |Real.log d| ≤ (Real.log K + N) * (1 + Real.log S) := by
  have hK0 : 0 < K := by linarith
  have hS0 : 0 < S := by linarith
  have hSN : 0 < S ^ N := by positivity
  have hd0 : 0 < d := by
    by_contra hcon
    have h : d ≤ 0 := not_lt.1 hcon
    have : K * S ^ N * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have h1 : 0 ≤ Real.log K := Real.log_nonneg hK
  have h2 : 0 ≤ Real.log S := Real.log_nonneg hS
  have hup : Real.log d ≤ Real.log K := Real.log_le_log hd0 hd
  have hlow : 0 ≤ Real.log K + N * Real.log S + Real.log d := by
    have := Real.log_nonneg hd2
    rwa [Real.log_mul (by positivity) hd0.ne', Real.log_mul hK0.ne' hSN.ne', Real.log_pow] at this
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg h1 h2, mul_nonneg hN h2]
  · nlinarith [mul_nonneg h1 h2, mul_nonneg hN h2]

theorem det_term {n a g m : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (F : (Fin n → ℂ) → Matrix (Fin m) (Fin g) ℂ) (hF : ContinuousAt F 0) (hr : (F 0).rank = m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ i : Fin n, i.val < a → z i ≠ 0) →
      (L.H z).IsHermitian →
      |Real.log (F z * L.H z * (F z)ᴴ).det.re| ≤ C * (1 + Real.log (Flat.logSize a z)) := by
  obtain ⟨ρ, K, N, hρ, -, h⟩ := Flat.logPeriods_subframe_det_bounds n a g Λ L m F hF hr
  have hK1 : 1 ≤ |K| + 1 := by linarith [abs_nonneg K]
  refine ⟨Real.log (|K| + 1) + N, add_nonneg (Real.log_nonneg hK1) (Nat.cast_nonneg N), ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℂ) hρ] with z hz h0 hH
  obtain ⟨h1, h2⟩ := h z hz h0
  have hS : 1 ≤ Flat.logSize a z := by
    have : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    simp only [Flat.logSize]
    linarith
  obtain ⟨D, hD⟩ : ∃ D, D = (F z * L.H z * (F z)ᴴ).det := ⟨_, rfl⟩
  rw [← hD] at h1 h2 ⊢
  have hHerm : (F z * L.H z * (F z)ᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose _ hH
  have hstar : star D = D := by
    rw [hD, ← Matrix.det_conjTranspose, hHerm.eq]
  have him : D.im = 0 := Complex.conj_eq_iff_im.1 hstar
  have hnorm : ‖D‖ = |D.re| := by
    have e : D = (D.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [e, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  have hlog : Real.log D.re = Real.log ‖D‖ := by
    rw [hnorm, Real.log_abs]
  rw [hlog]
  refine abs_log_le hS (h1.trans (by linarith [le_abs_self K])) (h2.trans ?_) hK1
  have : 0 ≤ Flat.logSize a z ^ N * ‖D‖ := by positivity
  have e : K * Flat.logSize a z ^ N * ‖D‖ ≤ (|K| + 1) * Flat.logSize a z ^ N * ‖D‖ := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) this
  exact e

theorem gram_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {g m : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (u : Fin m → Fin g → ℂ) :
    R.gram u = ((Matrix.of u) * R.Hm * (Matrix.of u)ᴴ)ᵀ := by
  ext i j
  rw [Matrix.mul_assoc]
  simp [RiemLat.gram, RiemLat.ip, Matrix.mul_apply, dotProduct, mulVec]

end GlobalTheory.CompanionTheory.Ar.Cusp.ULog

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open ULog in

theorem uLogBound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (L : ActPeriods E n a g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsCMFam σ → 1 ≤ m → IsEigFrames (Metric.ball 0 1) L.B σ b → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < ρ → 1 ≤ C * Flat.logSize a (expCover a w) * (L.riem w hw).lam1 ^ 2 ∧ (L.riem w hw).cuspW σ ≤ C * (1 + Real.log (Flat.logSize a (expCover a w))) ∧ |(L.riem w hw).logDet (fun τ i => b τ i (expCover a w))| ≤ C * (1 + Real.log (Flat.logSize a (expCover a w))) := by
  intro E _ _ _ n a g Λ _ _ Ψ _ L σ m b hσ hm hb
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hΨ : Nonempty Ψ := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    obtain ⟨s⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hσ.2 (s.comp (algebraMap (𝓞 E) E))
    simp only [IsEmpty.exists_iff, not_false_eq_true, iff_true] at this
  obtain ⟨τ₀⟩ := hΨ
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h
      exact absurd (Subsingleton.elim _ _) ((hb.2 0 h0ball τ₀).1.ne_zero ⟨0, hm⟩)
    · exact h
  haveI : Nontrivial Λ := by
    have hrk := L.rank
    exact Module.nontrivial_of_finrank_pos (R := ℤ) (by omega)
  obtain ⟨ρ₁, K, hρ₁, hK, hl⟩ := lattice_lower L.toLogPeriods
  have hdet : ∀ τ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      (∀ i : Fin n, i.val < a → z i ≠ 0) → (L.H z).IsHermitian →
      |Real.log ((Matrix.of fun i => b τ i z) * L.H z * (Matrix.of fun i => b τ i z)ᴴ).det.re| ≤
        C * (1 + Real.log (Flat.logSize a z)) := by
    intro τ
    refine det_term L.toLogPeriods (fun z => Matrix.of fun i => b τ i z) ?_ ?_
    · refine continuousAt_pi.2 fun i => ?_
      exact ((hb.1 τ i).continuousOn).continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
    · have := LinearIndependent.rank_matrix (M := Matrix.of fun i => b τ i 0) (hb.2 0 h0ball τ).1
      rwa [Fintype.card_fin] at this
  choose Cτ hCτ0 hCτ using hdet
  obtain ⟨ρ₂, hρ₂, hball⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_all.2 hCτ)
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = Real.log (2 * Fintype.card Ψ * m * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)))) := ⟨_, rfl⟩
  obtain ⟨Nn, hNn⟩ : ∃ Nn : ℝ, Nn = Fintype.card Ψ * m := ⟨_, rfl⟩
  have hNn0 : 0 ≤ Nn := by rw [hNn]; positivity
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hC2 : 0 ≤ Nn * (Real.log K + |D| + 1) := by positivity
  have hC3 : 0 ≤ ∑ τ, Cτ τ := Finset.sum_nonneg fun τ _ => hCτ0 τ
  refine ⟨min (min ρ₁ ρ₂) 1, K + Nn * (Real.log K + |D| + 1) + ∑ τ, Cτ τ,
    lt_min (lt_min hρ₁ hρ₂) one_pos, fun w hw hz => ?_⟩
  obtain ⟨z, hzdef⟩ : ∃ z, z = expCover a w := ⟨_, rfl⟩
  rw [← hzdef] at hz
  have hzρ₁ : ‖z‖ < ρ₁ := lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _))
  have hzρ₂ : z ∈ Metric.ball (0 : Fin n → ℂ) ρ₂ := by
    have : ‖z‖ < ρ₂ := lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_right _ _))
    simpa [dist_zero_right] using this
  have hz1 : z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    have : ‖z‖ < 1 := lt_of_lt_of_le hz (min_le_right _ _)
    simpa [dist_zero_right] using this
  have h0 : ∀ i : Fin n, i.val < a → z i ≠ 0 := by
    intro i hi
    rw [hzdef]
    simp [expCover, hi, Complex.exp_ne_zero]
  have hS : 1 ≤ Flat.logSize a z := by
    have : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    simp only [Flat.logSize]
    linarith
  have hT : 0 < K * Flat.logSize a z := by
    have : 0 < K := by linarith
    have : 0 < Flat.logSize a z := by linarith
    positivity
  have hlogS : 0 ≤ Real.log (Flat.logSize a z) := Real.log_nonneg hS
  obtain ⟨hl0, hl1⟩ := first_minimum_sq_lower_bound (L.riem w hw) hT (fun v hv => by
    have := hl w hw (by rw [← hzdef]; exact hzρ₁) v hv
    rw [← hzdef] at this
    have e : (L.riem w hw).normSq v = (L.P w v ⬝ᵥ L.H z *ᵥ star (L.P w v)).re := by
      rw [hzdef]
      rfl
    rw [e]
    exact this)
  have hrank : (L.riem w hw).HasRank σ m := by
    intro τ
    obtain ⟨hli, hsp⟩ := hb.2 z hz1 τ
    have e : (L.riem w hw).B = L.B z := by rw [hzdef]; rfl
    rw [e, ← hsp, finrank_span_eq_card hli, Fintype.card_fin]
  obtain ⟨-, -, -, -, hU⟩ := GlobalTheory.T.first_minimum_and_cusp_weight_bounds E g Λ Ψ (L.riem w hw) σ m hσ hrank hm
  rw [← hzdef]
  have hone : (1 : ℝ) ≤ 1 + Real.log (Flat.logSize a z) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hl2 : 0 ≤ Flat.logSize a z * (L.riem w hw).lam1 ^ 2 := by
      have : 0 ≤ Flat.logSize a z := by linarith
      positivity
    have h5 : 0 ≤ (Nn * (Real.log K + |D| + 1) + ∑ τ, Cτ τ) *
        (Flat.logSize a z * (L.riem w hw).lam1 ^ 2) := mul_nonneg (add_nonneg hC2 hC3) hl2
    nlinarith
  · have h2 := two_log_le hK hS hl0 hl1
    have h3 : (L.riem w hw).cuspW σ ≤ Nn * (Real.log K + Real.log (Flat.logSize a z) + D) := by
      rw [hNn, hDdef]
      refine hU.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith
    have h4 : Nn * (Real.log K + Real.log (Flat.logSize a z) + D) ≤
        Nn * (Real.log K + |D| + 1) * (1 + Real.log (Flat.logSize a z)) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hNn0
      have := le_abs_self D
      have := abs_nonneg D
      nlinarith
    have h5 : 0 ≤ (K + ∑ τ, Cτ τ) * (1 + Real.log (Flat.logSize a z)) := by
      have : 0 ≤ K := by linarith
      positivity
    nlinarith
  · have hterm : ∀ τ, |Real.log ((L.riem w hw).gram fun i => b τ i z).det.re| ≤
        Cτ τ * (1 + Real.log (Flat.logSize a z)) := by
      intro τ
      have hH : (L.H z).IsHermitian := by
        rw [hzdef]
        exact L.herm w hw
      have e : (L.riem w hw).Hm = L.H z := by rw [hzdef]; rfl
      rw [gram_eq, Matrix.det_transpose, e]
      exact hball z hzρ₂ τ h0 hH
    have h6 : |(L.riem w hw).logDet (fun τ i => b τ i z)| ≤
        ∑ τ, Cτ τ * (1 + Real.log (Flat.logSize a z)) := by
      simp only [RiemLat.logDet]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => hterm τ)
    rw [← Finset.sum_mul] at h6
    have h7 : 0 ≤ (K + Nn * (Real.log K + |D| + 1)) * (1 + Real.log (Flat.logSize a z)) := by
      have : 0 ≤ K := by linarith
      positivity
    nlinarith

end GlobalTheory.CompanionTheory.Ar.Cusp
