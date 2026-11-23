import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockRealGramComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace BlockRealGramComparison

open MvPolynomial MeasureTheory Filter Asymptotics Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped ComplexOrder ComplexConjugate Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem conj_pairValH (A : HermLine ι) (n : ℕ) (b b' : MvPolynomial (Σ k, ι k) ℚ) (z : (Σ k, ι k) → ℂ) :
    conj (pairValH A n b b' z) = pairValH A n b' b z := by
  simp only [pairValH, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

theorem pairValH_conjPt (A : HermLine ι) (hA : IsConjInvariantH A) (n : ℕ) (f f' : MRing ι)
    (z : (Σ k, ι k) → ℂ) :
    pairValH A n (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) f') (conjPt z) =
      conj (pairValH A n (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) f') z) := by
  have hh : A.h (conjPt z) = A.h z := hA z
  simp only [pairValH, SupBoundCount.eval_map_int_rat, SupBoundCount.eval_conjPt, hh, map_div₀, map_mul,
    Complex.conj_ofReal]

theorem blockGram_symm (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Σ k, ι k) ℚ)
    (k l : Fin r) : blockGram d n b l k = blockGram d n b k l := by
  simp only [blockGram, ← conj_pairValH d.A n (b k) (b l), integral_conj, Complex.conj_re]

theorem blockCGram_isHermitian (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ}
    (b : Fin r → MvPolynomial (Σ k, ι k) ℚ) : (blockCGram d n b).IsHermitian := by
  refine Matrix.IsHermitian.ext fun k l => ?_
  simp only [blockCGram, Complex.star_def, ← integral_conj, conj_pairValH]

theorem sum_quad {r : ℕ} (c w : Fin r → ℂ) (t : ℝ) :
    ∑ k, ∑ l, conj (c k) * (w k * conj (w l) / ((t ^ 2 : ℝ) : ℂ)) * c l =
      (((‖∑ k, conj (c k) * w k‖ / t) ^ 2 : ℝ) : ℂ) := by
  have hS : (((‖∑ k, conj (c k) * w k‖ / t) ^ 2 : ℝ) : ℂ) =
      (∑ k, conj (c k) * w k) * conj (∑ k, conj (c k) * w k) / ((t ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hS, map_sum, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [map_mul, Complex.conj_conj]
  ring

theorem quad_gram {X : Type*} [MeasurableSpace X] (μ : Measure X) (A : HermLine ι) (n : ℕ) {r : ℕ}
    (f : Fin r → MRing ι) (p : X → (Σ k, ι k) → ℂ) (M : Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ k l, M k l = ∫ x, pairValH A n (map (Int.castRingHom ℚ) (f k)) (map (Int.castRingHom ℚ) (f l)) (p x) ∂μ)
    (hi : ∀ k l, Integrable (fun x =>
      pairValH A n (map (Int.castRingHom ℚ) (f k)) (map (Int.castRingHom ℚ) (f l)) (p x)) μ)
    (c : Fin r → ℂ) :
    star c ⬝ᵥ (M *ᵥ c) =
      ((∫ x, (‖∑ k, conj (c k) * eval (p x) (map (Int.castRingHom ℂ) (f k))‖ / A.h (p x) ^ n) ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  calc star c ⬝ᵥ (M *ᵥ c)
      = ∑ k, ∑ l, ∫ x, conj (c k) * pairValH A n (map (Int.castRingHom ℚ) (f k))
          (map (Int.castRingHom ℚ) (f l)) (p x) * c l ∂μ := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, hM]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [integral_mul_const, integral_const_mul]
        ring
    _ = ∫ x, ∑ k, ∑ l, conj (c k) * pairValH A n (map (Int.castRingHom ℚ) (f k))
          (map (Int.castRingHom ℚ) (f l)) (p x) * c l ∂μ := by
        rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => ((hi k l).const_mul _).mul_const _]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_finsetSum _ fun l _ => ((hi k l).const_mul _).mul_const _]
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        have e : ∀ k l, pairValH A n (map (Int.castRingHom ℚ) (f k)) (map (Int.castRingHom ℚ) (f l)) (p x) =
            eval (p x) (map (Int.castRingHom ℂ) (f k)) * conj (eval (p x) (map (Int.castRingHom ℂ) (f l))) /
              (((A.h (p x) ^ n) ^ 2 : ℝ) : ℂ) := by
          intro k l
          simp only [pairValH, SupBoundCount.eval_map_int_rat]
          rw [← pow_mul, mul_comm n 2]
        simp only [e]
        exact sum_quad c (fun k => eval (p x) (map (Int.castRingHom ℂ) (f k))) _

theorem eval_comb {r : ℕ} (f : Fin r → MRing ι) (a : Fin r → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval z (∑ k, a k • map (Int.castRingHom ℂ) (f k) : MRingOver ℂ ι) =
      ∑ k, a k * eval z (map (Int.castRingHom ℂ) (f k)) := by
  simp only [map_sum, smul_eval]

theorem isMultiHomog_comb {r : ℕ} (f : Fin r → MRing ι) (a : Fin r → ℂ) {e : K → ℕ}
    (hf : ∀ k, IsMultiHomog (f k) e) :
    IsMultiHomog (∑ k, a k • map (Int.castRingHom ℂ) (f k) : MRingOver ℂ ι) e := by
  classical
  intro m hm
  obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
  exact hf k m (MvPolynomial.support_map_subset _ _ (MvPolynomial.support_smul hk))

theorem isHermitian_ofReal_smul {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.IsHermitian) (t : ℝ) :
    ((t : ℂ) • A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hA.eq, Complex.star_def, Complex.conj_ofReal]

theorem re_det_ofReal_smul {r : ℕ} (t : ℝ) (A : Matrix (Fin r) (Fin r) ℂ) :
    ((t : ℂ) • A).det.re = t ^ r * A.det.re := by
  rw [Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem re_det_le_of_quad {r : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef) (hB : B.IsHermitian)
    (t : ℝ) (h : ∀ c : Fin r → ℂ, (star c ⬝ᵥ (A *ᵥ c)).re ≤ t * (star c ⬝ᵥ (B *ᵥ c)).re) :
    A.det.re ≤ t ^ r * B.det.re := by
  have hsub := psd_sub_of_quad_le (isHermitian_ofReal_smul hB t) hA.isHermitian fun c => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
    exact h c
  have := GroundTheory.Heights₂.Heights.MCDet.re_det_mono hA hsub
  simp only [RCLike.re_to_complex] at this
  rwa [re_det_ofReal_smul] at this

theorem abs_sub_le (hR : BlockResolutionSupBound.Statement) (d : HSMBlockDatum D K ι Ω) :
    ∃ Kc : ℝ, 1 ≤ Kc ∧ ∀ n : ℕ, 1 ≤ n →
      |blockChi d n - blockCChi d n| ≤
        (finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) * (Real.log 2 + Real.log Kc + D * Real.log n) := by
  classical
  obtain ⟨C, hC⟩ := hR D K ι Ω d
  refine ⟨max (C ^ 2) 1, le_max_right _ _, fun n hn => ?_⟩
  set Kc := max (C ^ 2) 1 with hKc
  have hK1 : 1 ≤ Kc := le_max_right _ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogK := Real.log_nonneg hK1
  have hlogn := Real.log_nonneg hn1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL : 0 ≤ Real.log 2 + Real.log Kc + D * Real.log n := by positivity
  have hprob := d.vol.1
  by_cases h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d.y d.k₀ n p.2
  swap
  · simp only [blockChi, blockCChi, dif_neg h, sub_zero, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hL
  simp only [blockChi, blockCChi, dif_pos h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨r, b⟩ := p
  have hb : IsSecBasisM d.y d.k₀ n b := hp
  rw [SupBoundCount.finrank_secM hb]
  choose f hf hbf using hb.1
  have hbe : b = fun j => map (Int.castRingHom ℚ) (f j) := funext hbf
  subst hbe

  have hint := fun k l => SupBoundCount.integrable_blockPt d (SupBoundCount.pairValH_continuousOn d n (f k) (f l))
    (SupBoundCount.pairValH_torus d (hf k) (hf l))
  set G := blockCGram d n (fun j => map (Int.castRingHom ℚ) (f j)) with hG
  set H := blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) with hH
  set G₁ : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun k l => ∫ x, pairValH d.A n (map (Int.castRingHom ℚ) (f k))
    (map (Int.castRingHom ℚ) (f l)) (conjPt (blockPt d x)) ∂d.dV with hG₁
  set Hc : Matrix (Fin r) (Fin r) ℂ := H.map (fun t : ℝ => (t : ℂ)) with hHc

  set I₁ : (Fin r → ℂ) → ℝ := fun c => ∫ x, (‖∑ k, conj (c k) * eval (blockPt d x) (map (Int.castRingHom ℂ) (f k))‖ /
    d.A.h (blockPt d x) ^ n) ^ 2 ∂d.dV with hI₁
  set I₂ : (Fin r → ℂ) → ℝ := fun c => ∫ x, (‖∑ k, conj (c k) *
    eval (conjPt (blockPt d x)) (map (Int.castRingHom ℂ) (f k))‖ / d.A.h (conjPt (blockPt d x)) ^ n) ^ 2 ∂d.dV
    with hI₂
  have qG : ∀ c, star c ⬝ᵥ (G *ᵥ c) = ((I₁ c : ℝ) : ℂ) := fun c =>
    quad_gram d.dV d.A n f (blockPt d) G (fun _ _ => rfl) (fun k l => (hint k l).1) c
  have qG₁ : ∀ c, star c ⬝ᵥ (G₁ *ᵥ c) = ((I₂ c : ℝ) : ℂ) := fun c =>
    quad_gram d.dV d.A n f (fun x => conjPt (blockPt d x)) G₁ (fun _ _ => rfl) (fun k l => (hint k l).2) c

  have hHc2 : Hc = (1 / 2 : ℂ) • (G + G₁) := by
    ext k l
    have hc : G₁ k l = conj (G k l) := by
      simp only [hG₁, hG, Matrix.of_apply, blockCGram, ← integral_conj]
      congr 1
      funext x
      exact pairValH_conjPt d.A d.conjInv n (f k) (f l) _
    simp only [hHc, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, hc, smul_eq_mul]
    have hH' : H k l = (1 / 2) * ((G k l).re + (G₁ k l).re) := by
      simp only [hH, hG, hG₁, blockGram, blockCGram, Matrix.of_apply]
    rw [hH', hc, Complex.conj_re]
    apply Complex.ext <;> simp
  have qH : ∀ c, star c ⬝ᵥ (Hc *ᵥ c) = (((I₁ c + I₂ c) / 2 : ℝ) : ℂ) := by
    intro c
    rw [hHc2, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, qG, qG₁, smul_eq_mul]
    push_cast
    ring
  have hI₁0 : ∀ c, 0 ≤ I₁ c := fun c => integral_nonneg fun x => sq_nonneg _
  have hI₂0 : ∀ c, 0 ≤ I₂ c := fun c => integral_nonneg fun x => sq_nonneg _

  have hpow : ((n : ℝ) ^ ((D : ℝ) / 2)) ^ 2 = (n : ℝ) ^ D := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n),
      show (D : ℝ) / 2 * ((2 : ℕ) : ℝ) = (D : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hI₂le : ∀ c, I₂ c ≤ C ^ 2 * (n : ℝ) ^ D * I₁ c := by
    intro c
    set F : MRingOver ℂ ι := ∑ k, conj (c k) • map (Int.castRingHom ℂ) (f k) with hF
    have hFh : IsMultiHomog F (blockDeg d.k₀ n) := isMultiHomog_comb f _ hf
    have hL2 : blockL2NormComplex d n F ^ 2 = I₁ c := by
      rw [blockL2NormComplex, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _), hI₁]
      simp only [hF, eval_comb]
    have hpt : ∀ x, (‖∑ k, conj (c k) * eval (conjPt (blockPt d x)) (map (Int.castRingHom ℂ) (f k))‖ /
        d.A.h (conjPt (blockPt d x)) ^ n) ^ 2 ≤ C ^ 2 * (n : ℝ) ^ D * I₁ c := by
      intro x
      have h1 := hC n hn F hFh _ (SupBoundCount.conjPt_mem_mcPts (SupBoundCount.blockPt_mem d x))
      rw [hF, eval_comb] at h1
      have h0 : 0 ≤ ‖∑ k, conj (c k) * eval (conjPt (blockPt d x)) (map (Int.castRingHom ℂ) (f k))‖ /
          d.A.h (conjPt (blockPt d x)) ^ n :=
        div_nonneg (norm_nonneg _) (pow_nonneg (d.A.pos _ (SupBoundCount.conjPt_mem_mcPts
          (SupBoundCount.blockPt_mem d x)).1).le _)
      calc _ ≤ (C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n F) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = C ^ 2 * (n : ℝ) ^ D * I₁ c := by rw [mul_pow, mul_pow, hpow, hL2]
    have := integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
      (integrable_const (μ := d.dV) (C ^ 2 * (n : ℝ) ^ D * I₁ c)) (Eventually.of_forall hpt)
    simpa [hI₂] using this

  have hGpsd : G.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (blockCGram_isHermitian d n _) fun c => by
      rw [qG]; exact Complex.zero_le_real.mpr (hI₁0 c)
  have hHcherm : Hc.IsHermitian := by
    refine Matrix.IsHermitian.ext fun k l => ?_
    simp only [hHc, Matrix.map_apply, Complex.star_def, Complex.conj_ofReal, hH, blockGram_symm]
  have hHcpsd : Hc.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHcherm fun c => by
      rw [qH]; exact Complex.zero_le_real.mpr (by have := hI₁0 c; have := hI₂0 c; positivity)
  have hKn : (1 : ℝ) ≤ Kc * (n : ℝ) ^ D := by
    have : (1 : ℝ) ≤ (n : ℝ) ^ D := one_le_pow₀ hn1
    nlinarith
  have d1 := re_det_le_of_quad hGpsd hHcherm 2 fun c => by
    rw [qG, qH, Complex.ofReal_re, Complex.ofReal_re]
    linarith [hI₂0 c]
  have d2 := re_det_le_of_quad hHcpsd (blockCGram_isHermitian d n _) (Kc * (n : ℝ) ^ D) fun c => by
    rw [qG, qH, Complex.ofReal_re, Complex.ofReal_re]
    have h1 := hI₂le c
    have h2 := hI₁0 c
    have h3 : C ^ 2 * (n : ℝ) ^ D ≤ Kc * (n : ℝ) ^ D :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    nlinarith
  have hdet : Hc.det.re = H.det := by
    have := (RingHom.map_det Complex.ofRealHom H).symm
    rw [hHc]
    simp only [RingHom.mapMatrix_apply, Complex.ofRealHom_eq_coe] at this
    rw [show (H.map fun t : ℝ => (t : ℂ)) = H.map Complex.ofRealHom from rfl, this]
    simp
  rw [hdet] at d1 d2
  have hH0 : 0 ≤ H.det := by
    have := GroundTheory.Heights₂.Heights.MCDet.re_det_nonneg hHcpsd
    simp only [RCLike.re_to_complex] at this
    rwa [hdet] at this
  have hG0 : 0 ≤ G.det.re := by
    have := GroundTheory.Heights₂.Heights.MCDet.re_det_nonneg hGpsd
    simpa using this
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  rcases hH0.eq_or_lt with hz | hHpos
  ·
    have hGz : G.det.re = 0 := le_antisymm (by rw [← hz, mul_zero] at d1; exact d1) hG0
    rw [← hz, hGz, Real.log_zero, mul_zero, sub_self, abs_zero]
    exact mul_nonneg hr0 hL
  have hKn0 : 0 < Kc * (n : ℝ) ^ D := by linarith
  have hGpos : 0 < G.det.re := by
    by_contra hle
    push Not at hle
    have : (Kc * (n : ℝ) ^ D) ^ r * G.det.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    linarith
  have l1 : Real.log G.det.re ≤ r * Real.log 2 + Real.log H.det := by
    have := Real.log_le_log hGpos d1
    rwa [Real.log_mul (by positivity) hHpos.ne', Real.log_pow] at this
  have l2 : Real.log H.det ≤ r * (Real.log Kc + D * Real.log n) + Real.log G.det.re := by
    have := Real.log_le_log hHpos d2
    rwa [Real.log_mul (by positivity) hGpos.ne', Real.log_pow,
      Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
  have a1 := mul_nonneg hr0 hlog2
  have a2 := mul_nonneg hr0 (add_nonneg hlogK (mul_nonneg (Nat.cast_nonneg D) hlogn))
  rw [abs_le]
  constructor <;> nlinarith

theorem rank_le (hS : SupBoundBlock.Statement) (hN : SupBoundCount.Statement) (d : HSMBlockDatum D K ι Ω) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 1 ≤ n → (finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) ≤ A * (n : ℝ) ^ D := by
  obtain ⟨C, hC⟩ := hS D K ι Ω d
  set C' := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  refine ⟨2 * C' ^ 2, by positivity, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) ^ ((D : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
  have hc : 0 < C' * (n : ℝ) ^ ((D : ℝ) / 2) := by positivity
  have h := (hN D K ι Ω d n _ hc fun F hF z hz => (hC n hn F hF z hz).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hnp.le)
      (Real.sqrt_nonneg _))).1
  have hpow : ((n : ℝ) ^ ((D : ℝ) / 2)) ^ 2 = (n : ℝ) ^ D := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n),
      show (D : ℝ) / 2 * ((2 : ℕ) : ℝ) = (D : ℝ) by push_cast; ring, Real.rpow_natCast]
  calc (finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) ≤ 2 * (C' * (n : ℝ) ^ ((D : ℝ) / 2)) ^ 2 := h
    _ = 2 * C' ^ 2 * (n : ℝ) ^ D := by rw [mul_pow, hpow]; ring

theorem proof (hR : BlockResolutionSupBound.Statement) (hS : SupBoundBlock.Statement)
    (hN : SupBoundCount.Statement) : BlockRealGramComparison.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  obtain ⟨Kc, hK1, hK⟩ := abs_sub_le hR d
  obtain ⟨A, hA0, hA⟩ := rank_le hS hN d
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK := Real.log_nonneg hK1
  set B := (Real.log 2 + Real.log Kc) / Real.log 2 + D with hB
  have hB0 : 0 ≤ B := by positivity
  refine IsBigO.of_bound (A * B) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn0 := Real.log_nonneg hn1
  have hlog21 : Real.log 2 ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hlogn : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have hlog1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hL : Real.log 2 + Real.log Kc + D * Real.log n ≤ B * Real.log ((n : ℝ) + 1) := by
    have h1 : Real.log 2 + Real.log Kc ≤ (Real.log 2 + Real.log Kc) / Real.log 2 * Real.log ((n : ℝ) + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith
    have h2 : (D : ℝ) * Real.log n ≤ D * Real.log ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hlogn (Nat.cast_nonneg _)
    rw [hB, add_mul]
    linarith
  have hL0 : 0 ≤ Real.log 2 + Real.log Kc + D * Real.log n := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1))]
  calc |blockChi d n - blockCChi d n|
      ≤ (finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) * (Real.log 2 + Real.log Kc + D * Real.log n) := hK n hn
    _ ≤ (A * (n : ℝ) ^ D) * (B * Real.log ((n : ℝ) + 1)) := mul_le_mul (hA n hn) hL hL0 (by positivity)
    _ = A * B * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by ring

end

end BlockRealGramComparison

end GroundTheory.Heights₂.Heights.HilbertSamuel
