import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.DataHodge
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements.Twist

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix ComplexOrder

section Bundle

variable {Ω' : Type} [Field Ω'] {κ : Type}

def twistLat (x : κ → Ω') (i : κ) : AddSubgroup (Fin 2 → Ω') where
  carrier := {e | e 0 ∈ chartRing ℤ x i ∧ x i * e 1 ∈ chartRing ℤ x i}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [Pi.add_apply, mul_add]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem _, by rw [Pi.zero_apply, mul_zero]; exact zero_mem _⟩
  neg_mem' ha := ⟨neg_mem ha.1, by rw [Pi.neg_apply, mul_neg]; exact neg_mem ha.2⟩

def twW (x : κ → Ω') (i : κ) (q : Fin 2) : Ω' := if q = 0 then 1 else (x i)⁻¹

def twistVec (x : κ → Ω') (i : κ) (q : Fin 2) : Fin 2 → Ω' := twW x i q • Pi.single q 1

theorem sum_twistVec (x : κ → Ω') (i : κ) (a : Fin 2 → Ω') :
    ∑ q, a q • twistVec x i q = fun p => a p * twW x i p := by
  funext p
  fin_cases p <;> simp [twistVec, Fin.sum_univ_two, twW]

theorem twW_ne_zero {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) (q : Fin 2) : twW x i q ≠ 0 := by
  unfold twW
  split_ifs
  · exact one_ne_zero
  · exact inv_ne_zero hi

def twistBasis {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) : Module.Basis (Fin 2) Ω' (Fin 2 → Ω') :=
  (Pi.basisFun Ω' (Fin 2)).isUnitSMul (w := twW x i) fun q => (twW_ne_zero hi q).isUnit

theorem twistBasis_apply {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) (q : Fin 2) :
    twistBasis hi q = twistVec x i q := by
  rw [twistBasis, Module.Basis.isUnitSMul_apply, Pi.basisFun_apply]
  rfl

theorem twistVec_linearIndependent {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) :
    LinearIndependent Ω' (twistVec x i) := by
  have := (twistBasis hi).linearIndependent
  rwa [show ⇑(twistBasis hi) = twistVec x i from funext (twistBasis_apply hi)] at this

theorem twistVec_span {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) :
    Submodule.span Ω' (Set.range (twistVec x i)) = ⊤ := by
  have := (twistBasis hi).span_eq
  rwa [show ⇑(twistBasis hi) = twistVec x i from funext (twistBasis_apply hi)] at this

theorem twist_frame_iff {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) (e : Fin 2 → Ω') :
    (∃ n : ℕ, (1 : Ω') ^ n • e ∈ twistLat x i) ↔
      ∃ a : Fin 2 → Ω', (∀ q, ∃ n : ℕ, (1 : Ω') ^ n * a q ∈ chartRing ℤ x i) ∧
        e = ∑ q, a q • twistVec x i q := by
  simp only [one_pow, one_smul, one_mul, exists_const, sum_twistVec]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun q => if q = 0 then e 0 else x i * e 1, fun q => ?_, ?_⟩
    · fin_cases q
      · simpa using h0
      · simpa using h1
    · funext p
      fin_cases p
      · simp [twW]
      · simp [twW]
        field_simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨by simpa [twW] using ha 0, ?_⟩
    have h1 : x i * (a 1 * twW x i 1) = a 1 := by
      simp only [twW, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
      field_simp
    rw [h1]
    simpa using ha 1

def twistBundle (x : κ → Ω') : ChartBundle ℤ x 2 (Fin 2 → Ω') where
  lat := twistLat x
  stable i a ha e he := ⟨by simpa [smul_eq_mul] using mul_mem ha he.1,
    by simpa [smul_eq_mul, mul_left_comm] using mul_mem ha he.2⟩
  frame i hi := ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp,
    fun _ => ⟨twistVec x i, twistVec_linearIndependent hi, twistVec_span hi, twist_frame_iff hi⟩⟩
  overlap i j hi hj e he := by
    obtain ⟨m0, hm0⟩ := exists_pow_mul_mem_chartRing (o := ℤ) x i j hi he.1
    obtain ⟨m1, hm1⟩ := exists_pow_mul_mem_chartRing (o := ℤ) x i j hi he.2
    have hij : x i / x j ∈ chartRing ℤ x j := div_mem_chartRing x j i
    set r := x i / x j with hr
    refine ⟨m0 + m1 + 1, ?_, ?_⟩
    · have : (r ^ (m0 + m1 + 1) • e) 0 = r ^ (m1 + 1) * (r ^ m0 * e 0) := by
        rw [Pi.smul_apply, smul_eq_mul]; ring
      rw [this]
      exact mul_mem (pow_mem hij _) hm0
    · have hxx : x j * r = x i := mul_div_cancel₀ _ hj
      have : x j * (r ^ (m0 + m1 + 1) • e) 1 = r ^ m0 * (r ^ m1 * (x i * e 1)) := by
        rw [Pi.smul_apply, smul_eq_mul, ← hxx]
        ring
      rw [this]
      exact mul_mem (pow_mem hij _) hm1

end Bundle

abbrev ch (l : Fin 2) : Unit → Fin 2 := fun _ => l

theorem segreCoord_ch (l : Fin 2) : segreCoord yLine (ch l) = yLine ⟨(), l⟩ := by
  simp [segreCoord]

def tautSq (l : Fin 2) (z : (Σ _ : Unit, Fin 2) → ℂ) : ℝ :=
  (‖z ⟨(), 0⟩‖ ^ 2 + ‖z ⟨(), 1⟩‖ ^ 2) / ‖z ⟨(), l⟩‖ ^ 2

theorem tautSq_pos {l : Fin 2} {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : z ⟨(), l⟩ ≠ 0) : 0 < tautSq l z := by
  have hl : 0 < ‖z ⟨(), l⟩‖ ^ 2 := by positivity
  have : ‖z ⟨(), l⟩‖ ^ 2 ≤ ‖z ⟨(), 0⟩‖ ^ 2 + ‖z ⟨(), 1⟩‖ ^ 2 := by
    fin_cases l
    · simp only [Fin.zero_eta]; nlinarith [sq_nonneg ‖z ⟨(), 1⟩‖]
    · simp only [Fin.mk_one]; nlinarith [sq_nonneg ‖z ⟨(), 0⟩‖]
  exact div_pos (lt_of_lt_of_le hl this) hl

def twistGram (l : Fin 2) (z : (Σ _ : Unit, Fin 2) → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1, (tautSq l z : ℂ)]

theorem tautSq_chart (a : Fin 2) (t : Fin 1 → ℂ) : tautSq a (chartMap a t) = 1 + 4 * ‖t 0‖ ^ 2 := by
  fin_cases a <;> simp [tautSq, chartMap_apply] <;> ring

theorem isValueAt_ratio (l l' : Fin 2) {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : z ⟨(), l'⟩ ≠ 0) :
    IsValueAt yLine (yLine ⟨(), l⟩ / yLine ⟨(), l'⟩) z (z ⟨(), l⟩ / z ⟨(), l'⟩) := by
  have h := isMultiHomog_prod_X (ι := PBlk 2) (ch l)
  have h' := isMultiHomog_prod_X (ι := PBlk 2) (ch l')
  refine ⟨fun _ => 1, ∏ k, X ⟨k, ch l k⟩, ∏ k, X ⟨k, ch l' k⟩, h, h', ?_, ?_, ?_, ?_⟩
  · simpa using yLine_ne_zero ⟨(), l'⟩
  · simp only [aeval_X, Fintype.prod_unique]
    exact (div_mul_cancel₀ _ (yLine_ne_zero _)).symm
  · simpa using hz
  · simp

theorem contDiff_chartMap {n : WithTop ℕ∞} (a p : Fin 2) :
    ContDiff ℝ n (fun t : Fin 1 → ℂ => chartMap a t ⟨(), p⟩) := by
  have : (fun t : Fin 1 → ℂ => chartMap a t ⟨(), p⟩) = fun t => if p = a then 1 else 2 * t 0 := by
    funext t
    simp only [chartMap_apply]
  rw [this]
  split_ifs
  · exact contDiff_const
  · exact contDiff_const.mul (contDiff_apply ℝ ℂ (0 : Fin 1))

theorem contDiffAt_tautSq {n : WithTop ℕ∞} (l a : Fin 2) (t : Fin 1 → ℂ) (hz : chartMap a t ⟨(), l⟩ ≠ 0) :
    ContDiffAt ℝ n (fun t' => tautSq l (chartMap a t')) t := by
  have hn : ∀ p : Fin 2, ContDiff ℝ n (fun t' : Fin 1 → ℂ => ‖chartMap a t' ⟨(), p⟩‖ ^ 2) :=
    fun p => (contDiff_norm_sq ℝ).comp (contDiff_chartMap a p)
  exact (((hn 0).add (hn 1)).contDiffAt).div (hn l).contDiffAt (by positivity)

theorem inv_diag2 (s : ℝ) (hs : s ≠ 0) :
    (Matrix.diagonal ![(1 : ℂ), (s : ℂ)])⁻¹ = Matrix.diagonal ![(1 : ℂ), ((s⁻¹ : ℝ) : ℂ)] := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hs]

theorem psd_diag2 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (Matrix.diagonal ![(u : ℂ), (v : ℂ)]).PosSemidef := by
  refine Matrix.PosSemidef.diagonal fun i => ?_
  fin_cases i
  · simpa using Complex.zero_le_real.2 hu
  · simpa using Complex.zero_le_real.2 hv

theorem diagonal_two_sub_smul_one (s c : ℝ) :
    Matrix.diagonal ![(1 : ℂ), ((s : ℝ) : ℂ)] - ((c : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![((1 - c : ℝ) : ℂ), ((s - c : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sub_diag2 (C s : ℝ) :
    ((C : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Matrix.diagonal ![(1 : ℂ), ((s : ℝ) : ℂ)] =
      Matrix.diagonal ![((C - 1 : ℝ) : ℂ), ((C - s : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem norm_fderiv_taut (t : Fin 1 → ℂ) (ht : ‖t‖ < 1) :
    ‖fderiv ℝ (fun t' : Fin 1 → ℂ => (((1 + 4 * ‖t' 0‖ ^ 2 : ℝ)) : ℂ)) t‖ ≤ 8 := by
  have h1 : HasFDerivAt (fun t' : Fin 1 → ℂ => t' 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0) t := hasFDerivAt_apply 0 t
  have h2 := (h1.norm_sq.const_mul (4 : ℝ)).const_add 1
  have h3 : HasFDerivAt (fun t' : Fin 1 → ℂ => (((1 + 4 * ‖t' 0‖ ^ 2 : ℝ)) : ℂ)) _ t :=
    Complex.ofRealCLM.hasFDerivAt.comp t h2
  rw [h3.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hp : ‖(innerSL ℝ (t 0)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0)‖ ≤ ‖t 0‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.proj_apply]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm v 0) (norm_nonneg _))
  have ht0 : ‖t 0‖ ≤ 1 := (norm_le_pi_norm t 0).trans ht.le
  rw [Complex.ofRealCLM_norm, one_mul, norm_smul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
  norm_num
  nlinarith [norm_nonneg ((innerSL ℝ (t 0)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0))]

def twistMetric : HermMetric yLine (twistBundle (segreCoord yLine))
    (mcPts (mCoordIdeal yLine) \ ∅) lineChart where
  m := 2
  chart l := ch l
  fr _ := 1
  b l := twistVec (segreCoord yLine) (ch l)
  isFrame l := ⟨segreCoord_line_ne_zero l, one_mem _, one_ne_zero,
    twistVec_linearIndependent (segreCoord_line_ne_zero l), twist_frame_iff (segreCoord_line_ne_zero l)⟩
  gram := twistGram
  cover z hz := by
    obtain ⟨i, hi⟩ := mem_mcPts_line.1 hz.1
    exact ⟨i, inFrameDomain_line hi⟩
  posDef l z _ hl := by
    rw [twistGram, Matrix.posDef_diagonal_iff]
    intro p
    fin_cases p
    · simp
    · simpa using Complex.zero_lt_real.2 (tautSq_pos (hl.1 ()))
  compat l l' z hz hl hl' S hS Sz hSz := by
    have hzl : z ⟨(), l⟩ ≠ 0 := hl.1 ()
    have hzl' : z ⟨(), l'⟩ ≠ 0 := hl'.1 ()
    have hy : ∀ p : Fin 2, yLine ⟨(), p⟩ ≠ 0 := fun p => yLine_ne_zero _

    have hS' : ∀ p q, twW (segreCoord yLine) (ch l') q * (Pi.single q 1 : Fin 2 → Ω) p =
        S p q * twW (segreCoord yLine) (ch l) p := by
      intro p q
      have h := congrFun (hS q) p
      rw [sum_twistVec] at h
      simpa only [twistVec, Pi.smul_apply, smul_eq_mul] using h
    have hw : ∀ p, twW (segreCoord yLine) (ch l) p ≠ 0 := twW_ne_zero (segreCoord_line_ne_zero l)
    have n10 : (1 : Fin 2) ≠ 0 := by decide
    have e00 : S 0 0 = 1 := by
      have h := hS' 0 0
      simp only [twW, ↓reduceIte, Pi.single_eq_same, mul_one] at h
      exact h.symm
    have e10 : S 1 0 = 0 := by
      have h := hS' 1 0
      simp only [twW, ↓reduceIte, if_neg n10, Pi.single_eq_of_ne n10, mul_zero, segreCoord_ch] at h
      exact (mul_eq_zero.1 h.symm).resolve_right (inv_ne_zero (hy l))
    have e01 : S 0 1 = 0 := by
      have h := hS' 0 1
      simp only [twW, ↓reduceIte, if_neg n10, Pi.single_eq_of_ne n10.symm, mul_zero, mul_one] at h
      exact h.symm
    have e11 : S 1 1 = yLine ⟨(), l⟩ / yLine ⟨(), l'⟩ := by
      have h := hS' 1 1
      simp only [twW, if_neg n10, Pi.single_eq_same, mul_one, segreCoord_ch] at h
      calc
        S 1 1 = S 1 1 * (yLine ⟨(), l⟩)⁻¹ * yLine ⟨(), l⟩ := by rw [inv_mul_cancel_right₀ (hy l)]
        _ = yLine ⟨(), l⟩ / yLine ⟨(), l'⟩ := by rw [← h, div_eq_inv_mul]
    have v00 : Sz 0 0 = 1 := isValueAt_one hz.1 (e00 ▸ hSz 0 0)
    have v10 : Sz 1 0 = 0 := isValueAt_zero hz.1 (e10 ▸ hSz 1 0)
    have v01 : Sz 0 1 = 0 := isValueAt_zero hz.1 (e01 ▸ hSz 0 1)
    have v11 : Sz 1 1 = z ⟨(), l⟩ / z ⟨(), l'⟩ :=
      isValueAt_unique hz.1 (e11 ▸ hSz 1 1) (isValueAt_ratio l l' hzl')
    have key : (tautSq l' z : ℂ) = starRingEnd ℂ (z ⟨(), l⟩ / z ⟨(), l'⟩) * (tautSq l z : ℂ) *
        (z ⟨(), l⟩ / z ⟨(), l'⟩) := by
      have h1 : starRingEnd ℂ (z ⟨(), l⟩ / z ⟨(), l'⟩) * (tautSq l z : ℂ) * (z ⟨(), l⟩ / z ⟨(), l'⟩) =
          ((Complex.normSq (z ⟨(), l⟩ / z ⟨(), l'⟩) * tautSq l z : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
        ring
      rw [h1, Complex.normSq_eq_norm_sq, norm_div]
      congr 1
      have a1 : ‖z ⟨(), l⟩‖ ≠ 0 := norm_ne_zero_iff.2 hzl
      have a2 : ‖z ⟨(), l'⟩‖ ≠ 0 := norm_ne_zero_iff.2 hzl'
      simp only [tautSq]
      field_simp
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [twistGram, Matrix.mul_apply, Fin.sum_univ_two, v00, v10, v01, v11, key]
  torus l z _ _ c hc := by
    have hc0 : ‖c ()‖ ^ 2 ≠ 0 := by have := hc (); positivity
    simp only [twistGram, tautSq, torusSmul, norm_mul, mul_pow]
    rw [← mul_add, mul_div_mul_left _ _ hc0]
  conj l z _ _ := by
    have : tautSq l (conjVec z) = tautSq l z := by simp [tautSq, conjVec]
    rw [twistGram, twistGram, this, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext p
    fin_cases p <;> simp
  smooth a l t _ _ hd p q := by
    have hz : chartMap a t ⟨(), l⟩ ≠ 0 := hd.1 ()
    fin_cases p <;> fin_cases q
    · simp [twistGram]
      exact contDiffAt_const
    · simp [twistGram]
      exact contDiffAt_const
    · simp [twistGram]
      exact contDiffAt_const
    · simp only [twistGram, lineChart_γ, Fin.mk_one, Matrix.diagonal_apply_eq, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp t (contDiffAt_tautSq l a t hz)
  logBound a t₀ _ := by
    refine ⟨a, inFrameDomain_line (by rw [lineChart_γ, chartMap_apply, if_pos rfl]; exact one_ne_zero),
      1, one_pos, 1 / 5, by norm_num, 8, by norm_num, fun t _ ht _ _ => ?_⟩
    have ht0 : ‖t 0‖ ≤ ‖t‖ := norm_le_pi_norm t 0
    have hg : twistGram a ((lineChart a).γ t) = Matrix.diagonal ![(1 : ℂ), ((1 + 4 * ‖t 0‖ ^ 2 : ℝ) : ℂ)] := by
      rw [twistGram, lineChart_γ, tautSq_chart]
    have hs : (1 : ℝ) ≤ 1 + 4 * ‖t 0‖ ^ 2 := by nlinarith [norm_nonneg (t 0)]
    have hs5 : 1 + 4 * ‖t 0‖ ^ 2 ≤ (5 : ℝ) := by nlinarith [norm_nonneg (t 0)]
    rw [hg, inv_diag2 _ (by linarith), logR_lineChart]
    refine ⟨?_, ?_, fun p q => ?_⟩
    · rw [diagonal_two_sub_smul_one]
      refine psd_diag2 _ _ (by norm_num) ?_
      rw [sub_nonneg, le_inv_comm₀ (by norm_num) (by linarith)]
      linarith
    · rw [sub_diag2]
      have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      refine psd_diag2 _ _ (by nlinarith) ?_
      have : (1 + 4 * ‖t 0‖ ^ 2)⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hs
      nlinarith
    · have hC : (8 : ℝ) ≤ 8 * Real.exp (Real.exp 1 / 2) := by
        have := Real.one_le_exp (show (0 : ℝ) ≤ Real.exp 1 / 2 by positivity)
        nlinarith
      refine le_trans ?_ hC
      fin_cases p <;> fin_cases q
      · simp [twistGram, lineChart_γ]
      · simp [twistGram, lineChart_γ]
      · simp [twistGram, lineChart_γ]
      · have hf : (fun t' => twistGram a ((lineChart a).γ t') 1 1) =
            fun t' : Fin 1 → ℂ => (((1 + 4 * ‖t' 0‖ ^ 2 : ℝ)) : ℂ) := by
          funext t'
          simp [twistGram, lineChart_γ, tautSq_chart]
        simp only [Fin.mk_one]
        rw [hf]
        exact norm_fderiv_taut t ht

end GroundTheory.Heights₂.Heights.NineStatements.Twist
