import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffBoundaryParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ComplexOrder

noncomputable section

namespace GradDensSheetBound

theorem mdisc_cons_smul_tail {n : ℕ} (c : ℂ) (hc : c ≠ 0)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (W : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons X (fun i => c • W i) : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      c ^ n * mdisc (Fin.cons X W : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  have e : (Fin.cons X (fun i => c • W i) : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      fun k => (c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) *
        (Fin.cons (c⁻¹ • X) W : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k * 1 := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [smul_smul, hc]
    · simp
  rw [e, mdisc_mul_mul, mdisc_cons_smul_fst, Matrix.det_smul, det_one, Fintype.card_fin]
  field_simp
  ring

theorem vecMulVec_real_smul {m : ℕ} (r r' : ℝ) (a b : Fin m → ℂ) :
    vecMulVec ((r : ℂ) • a) (star ((r' : ℂ) • b)) = ((r * r' : ℝ) : ℂ) • vecMulVec a (star b) := by
  ext j k
  simp [vecMulVec_apply]
  ring

theorem two_abs_re_mdisc_le {n : ℕ} (x y : Fin (n + 1) → ℂ)
    (A W : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c : ℝ) (hc : 0 < c)
    (hle : ∀ i, ((c : ℂ) • W i - A i).PosSemidef) (hge : ∀ i, (A i + (c : ℂ) • W i).PosSemidef) :
    2 * |(mdisc (Fin.cons (vecMulVec x (star y)) A :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re| ≤
      3 ^ (n + 1) * c ^ n *
        ((mdisc (Fin.cons (vecMulVec x (star x)) W :
            Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re +
          (mdisc (Fin.cons (vecMulVec y (star y)) W :
            Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re) := by
  have hA : ∀ i, (A i).IsHermitian := fun i => by
    refine IsHermitian.ext fun j k => ?_
    have e1 := (hle i).1.apply j k
    have e2 := (hge i).1.apply j k
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_sub, star_add] at e1 e2
    linear_combination (e2 - e1) / 2
  have hNM : vecMulVec x (star x) + vecMulVec y (star y) -
      (vecMulVec x (star y) + vecMulVec y (star x)) = vecMulVec (x - y) (star (x - y)) := by
    ext j k; simp [vecMulVec_apply]; ring
  have hMN : vecMulVec x (star y) + vecMulVec y (star x) +
      (vecMulVec x (star x) + vecMulVec y (star y)) = vecMulVec (x + y) (star (x + y)) := by
    ext j k; simp [vecMulVec_apply]; ring
  have hB := norm_mdisc_le_of_abs_le
    (Fin.cons (vecMulVec x (star y) + vecMulVec y (star x)) A :
      Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (Fin.cons (vecMulVec x (star x) + vecMulVec y (star y)) (fun i => (c : ℂ) • W i))
    (fun k => by
      refine Fin.cases ?_ (fun i => ?_) k
      · simp only [Fin.cons_zero]; rw [hNM]; exact posSemidef_vecMulVec_self_star _
      · simpa using hle i)
    (fun k => by
      refine Fin.cases ?_ (fun i => ?_) k
      · simp only [Fin.cons_zero]; rw [hMN]; exact posSemidef_vecMulVec_self_star _
      · simpa using hge i)
  have hM : (mdisc (Fin.cons (vecMulVec x (star y) + vecMulVec y (star x)) A :
      Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re =
      2 * (mdisc (Fin.cons (vecMulVec x (star y)) A :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re := by
    have e := mdisc_cons_smul_add 1 1 (vecMulVec x (star y)) (vecMulVec y (star x)) A
    simp only [one_smul, one_mul] at e
    have hsw : vecMulVec y (star x) = (vecMulVec x (star y))ᴴ := by
      rw [conjTranspose_vecMulVec, star_star]
    rw [e, Complex.add_re, hsw, re_mdisc_cons_conjTranspose _ _ hA]
    ring
  have hN : (mdisc (Fin.cons (vecMulVec x (star x) + vecMulVec y (star y)) (fun i => (c : ℂ) • W i) :
      Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re =
      c ^ n * ((mdisc (Fin.cons (vecMulVec x (star x)) W :
            Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re +
          (mdisc (Fin.cons (vecMulVec y (star y)) W :
            Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re) := by
    have e := mdisc_cons_smul_add 1 1 (vecMulVec x (star x)) (vecMulVec y (star y)) W
    simp only [one_smul, one_mul] at e
    rw [mdisc_cons_smul_tail _ (Complex.ofReal_ne_zero.2 hc.ne'), e, ← Complex.ofReal_pow,
      Complex.re_ofReal_mul, Complex.add_re]
  have h1 := Complex.abs_re_le_norm (mdisc (Fin.cons (vecMulVec x (star y) + vecMulVec y (star x)) A :
      Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
  rw [hM, abs_mul, abs_two] at h1
  rw [hN] at hB
  linarith

theorem abs_le_of_forall_pos {X P Q K : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (h : ∀ u : ℝ, 0 < u → 2 * |X| ≤ K * (u * P + u⁻¹ * Q)) :
    |X| ≤ K * Real.sqrt P * Real.sqrt Q := by
  rcases hP.eq_or_lt with hP0 | hPpos
  · rw [← hP0, Real.sqrt_zero, mul_zero, zero_mul]
    by_contra hX
    push Not at hX
    have hkq : 0 ≤ K * Q := mul_nonneg hK hQ
    have hu := h ((K * Q + 1) / |X|) (by positivity)
    rw [← hP0, inv_div, mul_zero, zero_add] at hu
    have e : K * (|X| / (K * Q + 1) * Q) = K * Q * |X| / (K * Q + 1) := by ring
    rw [e, le_div_iff₀ (by positivity)] at hu
    nlinarith
  rcases hQ.eq_or_lt with hQ0 | hQpos
  · rw [← hQ0, Real.sqrt_zero, mul_zero]
    by_contra hX
    push Not at hX
    have hkp : 0 ≤ K * P := mul_nonneg hK hP
    have hu := h (|X| / (K * P + 1)) (by positivity)
    rw [← hQ0, mul_zero, add_zero] at hu
    have e : K * (|X| / (K * P + 1) * P) = K * P * |X| / (K * P + 1) := by ring
    rw [e, le_div_iff₀ (by positivity)] at hu
    nlinarith
  have hp := Real.sqrt_pos.2 hPpos
  have hq := Real.sqrt_pos.2 hQpos
  have hu := h (Real.sqrt Q / Real.sqrt P) (by positivity)
  have sP := Real.mul_self_sqrt hP
  have sQ := Real.mul_self_sqrt hQ
  have e1 : Real.sqrt Q / Real.sqrt P * P = Real.sqrt P * Real.sqrt Q := by
    calc Real.sqrt Q / Real.sqrt P * P = Real.sqrt Q / Real.sqrt P * (Real.sqrt P * Real.sqrt P) := by
          rw [sP]
      _ = Real.sqrt P * Real.sqrt Q := by rw [div_mul_eq_mul_div, div_eq_iff hp.ne']; ring
  have e2 : (Real.sqrt Q / Real.sqrt P)⁻¹ * Q = Real.sqrt P * Real.sqrt Q := by
    calc (Real.sqrt Q / Real.sqrt P)⁻¹ * Q = Real.sqrt P / Real.sqrt Q * (Real.sqrt Q * Real.sqrt Q) := by
          rw [inv_div, sQ]
      _ = Real.sqrt P * Real.sqrt Q := by rw [div_mul_eq_mul_div, div_eq_iff hq.ne']; ring
  have e : Real.sqrt Q / Real.sqrt P * P + (Real.sqrt Q / Real.sqrt P)⁻¹ * Q =
      2 * (Real.sqrt P * Real.sqrt Q) := by rw [e1, e2]; ring
  rw [e] at hu
  linarith

theorem hessC_pm_posSemidef {e : ℕ} (φ : (Fin e → ℂ) → ℝ) (x : Fin e → ℂ)
    (h2 : ContDiffAt ℝ 2 φ x) (M c : ℝ) (hM : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ M) (hc : M / 2 ≤ c) :
    ((c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ) - hessC φ x).PosSemidef ∧
      (hessC φ x + (c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ)).PosSemidef := by
  have hs : IsSymmSndFDerivAt ℝ φ x := h2.isSymmSndFDerivAt (by simp)
  have hH := hessC_isHermitian φ x h2
  have hM0 : 0 ≤ M := (ContinuousLinearMap.opNorm_nonneg _).trans hM
  have hI : ((c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  have hq : ∀ ξ : Fin e → ℂ, (star ξ ⬝ᵥ (hessC φ x *ᵥ ξ)).im = 0 ∧
      |(star ξ ⬝ᵥ (hessC φ x *ᵥ ξ)).re| ≤ c * ∑ j, ‖ξ j‖ ^ 2 := by
    intro ξ
    set H := fderiv ℝ (fderiv ℝ φ) x with hHdef
    have key : star ξ ⬝ᵥ (hessC φ x *ᵥ ξ) = leviC H (star ξ) (star ξ) := by
      simp only [dotProduct, mulVec, hessC_eq_leviC, sum_leviC_mul]
      exact sum_mul_leviC _ (star ξ) (star ξ)
    rw [key]
    refine ⟨by simp only [leviC, hHdef]; rw [hs (star ξ) (Complex.I • star ξ)]; simp, ?_⟩
    have hre : (leviC H (star ξ) (star ξ)).re =
        (H (star ξ) (star ξ) + H (Complex.I • star ξ) (Complex.I • star ξ)) / 4 := by
      simp [leviC]
    have hn : ‖star ξ‖ ^ 2 ≤ ∑ j, ‖ξ j‖ ^ 2 := by
      have hle : ‖star ξ‖ ≤ Real.sqrt (∑ j, ‖ξ j‖ ^ 2) := by
        refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
        rw [Pi.star_apply, norm_star]
        exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun j => ‖ξ j‖ ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ j))
      calc ‖star ξ‖ ^ 2 ≤ Real.sqrt (∑ j, ‖ξ j‖ ^ 2) ^ 2 := by gcongr
        _ = _ := Real.sq_sqrt (by positivity)
    have hIa : ‖Complex.I • star ξ‖ = ‖star ξ‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have h1 : |H (star ξ) (star ξ)| ≤ M * ‖star ξ‖ ^ 2 := by
      have := H.le_opNorm₂ (star ξ) (star ξ)
      rw [Real.norm_eq_abs] at this
      nlinarith [mul_le_mul_of_nonneg_right hM (sq_nonneg ‖star ξ‖)]
    have h2 : |H (Complex.I • star ξ) (Complex.I • star ξ)| ≤ M * ‖star ξ‖ ^ 2 := by
      have := H.le_opNorm₂ (Complex.I • star ξ) (Complex.I • star ξ)
      rw [Real.norm_eq_abs, hIa] at this
      nlinarith [mul_le_mul_of_nonneg_right hM (sq_nonneg ‖star ξ‖)]
    rw [hre, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by norm_num)]
    have h3 := abs_add_le (H (star ξ) (star ξ)) (H (Complex.I • star ξ) (Complex.I • star ξ))
    nlinarith [mul_le_mul_of_nonneg_left hn hM0, mul_le_mul_of_nonneg_right hc
      (Finset.sum_nonneg (fun j _ => sq_nonneg ‖ξ j‖) : 0 ≤ ∑ j, ‖ξ j‖ ^ 2)]
  have hval : ∀ ξ : Fin e → ℂ, star ξ ⬝ᵥ (((c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ)) *ᵥ ξ) =
      ((c * ∑ j, ‖ξ j‖ ^ 2 : ℝ) : ℂ) := by
    intro ξ
    have hmv : ((c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ)) *ᵥ ξ = (c : ℂ) • ξ := by
      ext j; simp [mulVec, dotProduct, Matrix.one_apply]
    rw [hmv, dotProduct_smul, smul_eq_mul]
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  constructor
  · refine PosSemidef.of_dotProduct_mulVec_nonneg (hI.sub hH) fun ξ => ?_
    obtain ⟨him, hre⟩ := hq ξ
    rw [sub_mulVec, dotProduct_sub, hval, Complex.nonneg_iff]
    refine ⟨?_, ?_⟩
    · simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [(abs_le.1 hre).2]
    · rw [Complex.sub_im, Complex.ofReal_im, him]; norm_num
  · refine PosSemidef.of_dotProduct_mulVec_nonneg (hH.add hI) fun ξ => ?_
    obtain ⟨him, hre⟩ := hq ξ
    rw [add_mulVec, dotProduct_add, hval, Complex.nonneg_iff]
    refine ⟨?_, ?_⟩
    · simp only [Complex.add_re, Complex.ofReal_re]
      linarith [(abs_le.1 hre).1]
    · rw [Complex.add_im, Complex.ofReal_im, him]; norm_num

theorem exists_hessC_bound {n d : ℕ} (φ : Fin d → (Fin n → ℂ) → ℝ) (U K : Set (Fin n → ℂ))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hφ : ∀ i, ContDiffOn ℝ 2 (φ i) U) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ i,
      ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - hessC (φ i) x).PosSemidef ∧
        (hessC (φ i) x + (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  have hcont : ContinuousOn (fun x => ∑ i, ‖fderiv ℝ (fderiv ℝ (φ i)) x‖) U :=
    continuousOn_finsetSum _ fun i _ =>
      (((hφ i).fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU
        le_rfl).norm
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKU)
  refine ⟨max M 0 / 2 + 1, by positivity, fun x hx i => ?_⟩
  have h2 : ContDiffAt ℝ 2 (φ i) x := (hφ i).contDiffAt (hU.mem_nhds (hKU hx))
  have hMi : ‖fderiv ℝ (fderiv ℝ (φ i)) x‖ ≤ max M 0 :=
    (((Finset.single_le_sum (f := fun i => ‖fderiv ℝ (fderiv ℝ (φ i)) x‖)
      (fun i _ => ContinuousLinearMap.opNorm_nonneg _) (Finset.mem_univ i)).trans
        ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM x hx))))).trans
      (le_max_left _ _)
  exact hessC_pm_posSemidef (φ i) x h2 _ _ hMi (by linarith)

theorem posSemidef_transpose_mul_mul_conj {n m : ℕ} (J : Matrix (Fin n) (Fin m) ℂ)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) :
    (Jᵀ * P * J.map (starRingEnd ℂ)).PosSemidef := by
  have e : Jᵀ = (J.map (starRingEnd ℂ))ᴴ := by
    ext i j; simp [conjTranspose_apply]
  rw [e]
  exact hP.conjTranspose_mul_mul_same _

end GradDensSheetBound

theorem GradDensSheetBound.proof : GradDensSheetBound.Statement := by
  intro n d φ U K hU hK hKU hφ
  obtain ⟨c, hc, hcK⟩ := exists_hessC_bound φ U K hU hK hKU hφ
  refine ⟨3 ^ (d + 1) * c ^ d, by positivity, fun s y v w hs hsy => ?_⟩
  have hE : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hW : hessC (euclPot ∘ s) y = (jacC s y)ᵀ * (1 : Matrix (Fin n) (Fin n) ℂ) * (jacC s y).map (starRingEnd ℂ) := by
    have e : (euclPot : (Fin n → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i) := by
      funext w; simp [euclPot, Complex.normSq_eq_norm_sq]
    rw [hessC_comp _ _ _ hs hE, e, hessC_sum_normSq]
  have hA : ∀ i, hessC (φ i ∘ s) y =
      (jacC s y)ᵀ * hessC (φ i) (s y) * (jacC s y).map (starRingEnd ℂ) := fun i =>
    hessC_comp _ _ _ hs ((hφ i).contDiffAt (hU.mem_nhds (hKU hsy)))
  have hle : ∀ i, ((c : ℂ) • hessC (euclPot ∘ s) y - hessC (φ i ∘ s) y).PosSemidef := by
    intro i
    have e : (c : ℂ) • ((jacC s y)ᵀ * (1 : Matrix (Fin n) (Fin n) ℂ) * (jacC s y).map (starRingEnd ℂ)) -
        (jacC s y)ᵀ * hessC (φ i) (s y) * (jacC s y).map (starRingEnd ℂ) =
        (jacC s y)ᵀ * ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - hessC (φ i) (s y)) * (jacC s y).map (starRingEnd ℂ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hW, hA, e]
    exact posSemidef_transpose_mul_mul_conj _ (hcK _ hsy i).1
  have hge : ∀ i, (hessC (φ i ∘ s) y + (c : ℂ) • hessC (euclPot ∘ s) y).PosSemidef := by
    intro i
    have e : (jacC s y)ᵀ * hessC (φ i) (s y) * (jacC s y).map (starRingEnd ℂ) +
        (c : ℂ) • ((jacC s y)ᵀ * (1 : Matrix (Fin n) (Fin n) ℂ) * (jacC s y).map (starRingEnd ℂ)) =
        (jacC s y)ᵀ * (hessC (φ i) (s y) + (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) * (jacC s y).map (starRingEnd ℂ) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hW, hA, e]
    exact posSemidef_transpose_mul_mul_conj _ (hcK _ hsy i).2
  have hWpsd : (hessC (euclPot ∘ s) y).PosSemidef := by
    rw [hW]; exact posSemidef_transpose_mul_mul_conj _ PosSemidef.one
  unfold gradDens
  simp only [gradMat_eq_vecMulVec]
  generalize (fun j => dz j (cplx v) y) = a
  generalize (fun k => dz k (cplx w) y) = b
  generalize hessC (euclPot ∘ s) y = W at hle hge hWpsd ⊢
  have hN : (0 : ℝ) ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) := by positivity
  set N : ℝ := ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) with hNdef
  set X := (mdisc (Fin.cons (vecMulVec a (star b)) (fun i => hessC (φ i ∘ s) y) :
    Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)).re with hXdef
  set P := (mdisc (Fin.cons (vecMulVec a (star a)) (fun _ : Fin d => W) :
    Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)).re with hPdef
  set Q := (mdisc (Fin.cons (vecMulVec b (star b)) (fun _ : Fin d => W) :
    Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)).re with hQdef
  have hP : 0 ≤ P := re_mdisc_cons_vecMulVec_nonneg a (fun _ : Fin d => W) (fun _ => hWpsd)
  have hQ : 0 ≤ Q := re_mdisc_cons_vecMulVec_nonneg b (fun _ : Fin d => W) (fun _ => hWpsd)
  have key : |X| ≤ 3 ^ (d + 1) * c ^ d * Real.sqrt P * Real.sqrt Q := by
    refine abs_le_of_forall_pos hP hQ (by positivity) fun u hu => ?_
    have hsu := Real.sqrt_pos.2 hu
    have ht := two_abs_re_mdisc_le ((Real.sqrt u : ℂ) • a) ((((Real.sqrt u)⁻¹ : ℝ) : ℂ) • b)
      (fun i => hessC (φ i ∘ s) y) (fun _ => W) c hc hle hge
    rw [vecMulVec_real_smul, vecMulVec_real_smul, vecMulVec_real_smul, mul_inv_cancel₀ hsu.ne',
      Complex.ofReal_one, one_smul, mdisc_cons_smul_fst, mdisc_cons_smul_fst, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul, Real.mul_self_sqrt hu.le, ← mul_inv, Real.mul_self_sqrt hu.le] at ht
    exact ht
  rw [abs_mul, abs_of_nonneg hN, Real.sqrt_mul hN, Real.sqrt_mul hN]
  have sN := Real.mul_self_sqrt hN
  calc N * |X| ≤ N * (3 ^ (d + 1) * c ^ d * Real.sqrt P * Real.sqrt Q) :=
        mul_le_mul_of_nonneg_left key hN
    _ = 3 ^ (d + 1) * c ^ d * (Real.sqrt N * Real.sqrt P) * (Real.sqrt N * Real.sqrt Q) := by
        linear_combination (-(3 ^ (d + 1) * c ^ d * Real.sqrt P * Real.sqrt Q)) * sN

end

end GroundTheory.Heights₂.Heights
