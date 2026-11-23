import Formalism.SizeWindowBrackets.MatrixFamilyBoundsOfCardEqCeil
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TraceConjTransposeMulSelf
import Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice

open Matrix Module NumberField
open scoped ComplexOrder

namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance

open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare

noncomputable section

theorem unitary_dimension : UniDim := by
  intro m n V h
  have h1 : (Vᴴ * V).trace = (n : ℂ) := by rw [h.1]; simp
  have h2 : (V * Vᴴ).trace = (m : ℂ) := by rw [h.2]; simp
  rw [trace_mul_comm] at h1
  have : (m : ℂ) = n := by rw [← h2, h1]
  exact_mod_cast this

lemma hsSq_left {a a' b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) (S : Matrix (Fin a') (Fin a) ℂ)
    (hS : Sᴴ * S = 1) : hsSq (S * M) = hsSq M := by
  rw [hsSq_eq_re, hsSq_eq_re, conjTranspose_mul]
  have : Mᴴ * Sᴴ * (S * M) = Mᴴ * (Sᴴ * S) * M := by simp only [Matrix.mul_assoc]
  rw [this, hS, Matrix.mul_one]

lemma hsSq_right {a b b' : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) (T : Matrix (Fin b) (Fin b') ℂ)
    (hT : T * Tᴴ = 1) : hsSq (M * T) = hsSq M := by
  rw [← hsSq_conjTranspose (M * T), conjTranspose_mul, hsSq_left _ _ (by simpa using hT),
    hsSq_conjTranspose]

theorem hilbert_schmidt_unitary_invariant : HsUni := by
  intro a b a' b' M S T hS hT
  rw [hsSq_right _ _ hT, hsSq_left _ _ hS]

section Fam

variable {ι : Type} [Fintype ι] {D D' : ℕ} {d : ι → ℕ}

lemma norm_phase (c : ι → ℂ) (hc : ∀ u, c u ≠ 0) (u u' : ι) : ‖phase c u u'‖ = 1 := by
  unfold phase
  have h1 : 0 < ‖c u‖ := norm_pos_iff.mpr (hc u)
  have h2 : 0 < ‖c u'‖ := norm_pos_iff.mpr (hc u')
  rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos h1 h2)]
  exact div_self (mul_pos h1 h2).ne'

lemma phase_self (c : ι → ℂ) (hc : ∀ u, c u ≠ 0) (u : ι) : phase c u u = 1 := by
  unfold phase
  have h1 : (‖c u‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr (hc u)).ne'
  rw [Complex.conj_mul']
  push_cast
  field_simp

lemma sqrt_gaTw (ga : ι → ℝ) (c : ι → ℂ) (hc : ∀ u, c u ≠ 0) (u u' : ι) :
    Real.sqrt (gaTw ga c u * gaTw ga c u') = Real.sqrt (ga u * ga u') / (‖c u‖ * ‖c u'‖) := by
  unfold gaTw
  have h1 : 0 < ‖c u‖ := norm_pos_iff.mpr (hc u)
  have h2 : 0 < ‖c u'‖ := norm_pos_iff.mpr (hc u')
  have : ga u / ‖c u‖ ^ 2 * (ga u' / ‖c u'‖ ^ 2) = ga u * ga u' / (‖c u‖ * ‖c u'‖) ^ 2 := by
    field_simp
  rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]

lemma Kp_tw (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (c : ι → ℂ)
    (V : Matrix (Fin D') (Fin D) ℂ) (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ)
    (hc : ∀ u, c u ≠ 0) (hV : Vᴴ * V = 1) (u u' : ι) :
    Kp (Btwist B c V U) (gaTw ga c) u u' = phase c u u' • ((U u)ᴴ * Kp B ga u u' * U u') := by
  unfold Kp
  rw [sqrt_gaTw ga c hc]
  unfold Btwist phase
  have hm : (V * B u * U u)ᴴ * (V * B u' * U u') = (U u)ᴴ * ((B u)ᴴ * B u') * U u' := by
    rw [conjTranspose_mul, conjTranspose_mul]
    have : (U u)ᴴ * ((B u)ᴴ * Vᴴ) * (V * B u' * U u')
        = (U u)ᴴ * ((B u)ᴴ * (Vᴴ * V) * B u') * U u' := by simp only [Matrix.mul_assoc]
    rw [this, hV, Matrix.mul_one]
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hm, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, smul_smul, smul_smul]
  congr 1
  push_cast
  simp only [Complex.star_def]
  ring

lemma Kd_tw (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (c : ι → ℂ)
    (V : Matrix (Fin D') (Fin D) ℂ) (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ)
    (hc : ∀ u, c u ≠ 0) (hV : Vᴴ * V = 1) (u : ι) :
    Kd (Btwist B c V U) (gaTw ga c) u = (U u)ᴴ * Kd B ga u * U u := by
  unfold Kd
  rw [Kp_tw B ga c V U hc hV, phase_self c hc, one_smul]

lemma Kd_tw_sub (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (c : ι → ℂ)
    (V : Matrix (Fin D') (Fin D) ℂ) (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ)
    (hc : ∀ u, c u ≠ 0) (hV : Vᴴ * V = 1) (hU : ∀ u, IsUni (U u)) (u : ι) :
    Kd (Btwist B c V U) (gaTw ga c) u - 1 = (U u)ᴴ * (Kd B ga u - 1) * U u := by
  rw [Kd_tw B ga c V U hc hV, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, (hU u).1]

lemma hs_Kp_tw (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (c : ι → ℂ)
    (V : Matrix (Fin D') (Fin D) ℂ) (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ)
    (hc : ∀ u, c u ≠ 0) (hV : Vᴴ * V = 1) (hU : ∀ u, IsUni (U u)) (u u' : ι) :
    hsSq (Kp (Btwist B c V U) (gaTw ga c) u u') = hsSq (Kp B ga u u') := by
  rw [Kp_tw B ga c V U hc hV, hsSq_smul, norm_phase c hc, one_pow, one_mul]
  exact hilbert_schmidt_unitary_invariant _ _ _ _ _ _ _ (by simpa using (hU u).2) (hU u').2

lemma hs_Kd_tw (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (c : ι → ℂ)
    (V : Matrix (Fin D') (Fin D) ℂ) (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ)
    (hc : ∀ u, c u ≠ 0) (hV : Vᴴ * V = 1) (hU : ∀ u, IsUni (U u)) (u : ι) :
    hsSq (Kd (Btwist B c V U) (gaTw ga c) u - 1) = hsSq (Kd B ga u - 1) := by
  rw [Kd_tw_sub B ga c V U hc hV hU]
  exact hilbert_schmidt_unitary_invariant _ _ _ _ _ _ _ (by simpa using (hU u).2) (hU u).2

lemma Qm_tw (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (c : ι → ℂ)
    (V : Matrix (Fin D') (Fin D) ℂ) (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ)
    (hc : ∀ u, c u ≠ 0) (hU : ∀ u, IsUni (U u)) :
    Qm (Btwist B c V U) (gaTw ga c) = V * Qm B ga * Vᴴ := by
  unfold Qm
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold Btwist gaTw
  have hm : (V * B u * U u) * (V * B u * U u)ᴴ = V * (B u * (B u)ᴴ) * Vᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul]
    have : V * B u * U u * ((U u)ᴴ * ((B u)ᴴ * Vᴴ)) = V * (B u * (U u * (U u)ᴴ) * (B u)ᴴ) * Vᴴ := by
      simp only [Matrix.mul_assoc]
    rw [this, (hU u).2, Matrix.mul_one]
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hm, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, smul_smul]
  congr 1
  have h1 : (‖c u‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr (hc u)).ne'
  have h2 : c u * star (c u) = (‖c u‖ : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.mul_conj']
  push_cast
  rw [mul_assoc, h2]
  field_simp

lemma trace_conj (V : Matrix (Fin D') (Fin D) ℂ) (hV : Vᴴ * V = 1) (Q : Matrix (Fin D) (Fin D) ℂ) :
    (V * Q * Vᴴ).trace = Q.trace := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

lemma conj_sq (V : Matrix (Fin D') (Fin D) ℂ) (hV : Vᴴ * V = 1) (Q : Matrix (Fin D) (Fin D) ℂ) :
    (V * Q * Vᴴ) * (V * Q * Vᴴ) = V * (Q * Q) * Vᴴ := by
  have : V * Q * Vᴴ * (V * Q * Vᴴ) = V * (Q * (Vᴴ * V) * Q) * Vᴴ := by
    simp only [Matrix.mul_assoc]
  rw [this, hV, Matrix.mul_one]

end Fam

theorem twist_hilbert_schmidt : TwHS := by
  intro ι _ D D' d B ga c V U hc hV hU
  exact ⟨hs_Kp_tw B ga c V U hc hV.1 hU, hs_Kd_tw B ga c V U hc hV.1 hU⟩

theorem twist_quadratic_form : TwQ := by
  intro ι _ D D' d B ga c V U hc hV hU
  have h := Qm_tw B ga c V U hc hU
  refine ⟨h, ?_, ?_⟩
  · rw [h, trace_conj V hV.1]
  · rw [h, conj_sq V hV.1, trace_conj V hV.1]

theorem twist_invariance : TwInv := by
  intro ι _ D D' d B ga c V U hc hV hU
  obtain ⟨-, hq1, hq2⟩ := twist_quadratic_form ι D D' d B ga c V U hc hV hU
  obtain ⟨hk1, hk2⟩ := twist_hilbert_schmidt ι D D' d B ga c V U hc hV hU
  have hD : D' = D := unitary_dimension _ _ V hV
  refine ⟨fun u => ?_, fun η => ?_, fun e => ?_, fun Dstar η0 η1 e0 => ?_⟩
  · unfold gaTw
    have h1 : 0 < ‖c u‖ ^ 2 := by have := norm_pos_iff.mpr (hc u); positivity
    exact div_pos_iff_of_pos_right h1
  · unfold F1; rw [hq1, hq2, hD]
  · unfold F2; simp only [hk2]
  · unfold InputS; simp only [hk1, hk2, hD]

section Inv

variable {n : ℕ}

end Inv

lemma gaTw_one {ι : Type} (ga : ι → ℝ) : gaTw ga (fun _ => (1 : ℂ)) = ga := by
  funext u; simp [gaTw]

theorem block_count_valid : RowsCount := by
  intro Dall D del h
  rw [le_div_iff₀ (by linarith), mul_comm]

section Frame

variable {Dall D D1 : ℕ}

lemma frame_orth (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (h : OrthFrame J J1) : Jᴴ * J1 = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : Jᴴ * (J * Jᴴ + J1 * J1ᴴ) * J1 = Jᴴ * J1 + Jᴴ * J1 := by
    rw [Matrix.mul_add, Matrix.add_mul]
    have a1 : Jᴴ * (J * Jᴴ) * J1 = (Jᴴ * J) * (Jᴴ * J1) := by simp only [Matrix.mul_assoc]
    have a2 : Jᴴ * (J1 * J1ᴴ) * J1 = (Jᴴ * J1) * (J1ᴴ * J1) := by simp only [Matrix.mul_assoc]
    rw [a1, a2, h1, h2, Matrix.one_mul, Matrix.mul_one]
  rw [h3, Matrix.mul_one] at e
  calc Jᴴ * J1 = (Jᴴ * J1 + Jᴴ * J1) - Jᴴ * J1 := by abel
    _ = Jᴴ * J1 - Jᴴ * J1 := by rw [← e]
    _ = 0 := sub_self _

lemma frame_orth' (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (h : OrthFrame J J1) : J1ᴴ * J = 0 := by
  have : (Jᴴ * J1)ᴴ = J1ᴴ * J := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [← this, frame_orth J J1 h, conjTranspose_zero]

lemma frame_dim (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (h : OrthFrame J J1) : Dall = D + D1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have t := congrArg Matrix.trace h3
  rw [trace_add, trace_mul_comm J, trace_mul_comm J1, h1, h2] at t
  simp only [trace_one, Fintype.card_fin] at t
  exact_mod_cast t.symm

lemma Wfr_mul {m : Type} (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (X : Matrix (Fin Dall) m ℂ) :
    Wfr J J1 * X = (Matrix.fromRows (Jᴴ * X) (J1ᴴ * X)).submatrix finSumFinEquiv.symm id := by
  unfold Wfr
  rw [← Matrix.fromRows_mul]
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]

lemma Wfr_H (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) :
    (Wfr J J1)ᴴ = (Matrix.fromCols J J1).submatrix id finSumFinEquiv.symm := by
  unfold Wfr
  rw [conjTranspose_submatrix, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_conjTranspose, conjTranspose_conjTranspose]

lemma rows_mul_WfrH {a b : ℕ} (X : Matrix (Fin a) (Fin Dall) ℂ) (X1 : Matrix (Fin b) (Fin Dall) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) :
    (Matrix.fromRows X X1).submatrix finSumFinEquiv.symm id * (Wfr J J1)ᴴ
      = (Matrix.fromBlocks (X * J) (X * J1) (X1 * J) (X1 * J1)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [Wfr_H, ← Matrix.fromRows_mul_fromCols]
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]

lemma Wfr_uni (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (h : OrthFrame J J1) : IsUni (Wfr J J1) := by
  constructor
  · rw [Wfr_H]
    unfold Wfr
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, h.2.2]
    simp
  · show (Matrix.fromRows Jᴴ J1ᴴ).submatrix finSumFinEquiv.symm id * (Wfr J J1)ᴴ = 1
    rw [rows_mul_WfrH, h.1, h.2.1, frame_orth J J1 h, frame_orth' J J1 h, Matrix.fromBlocks_one,
      Matrix.submatrix_one_equiv]

end Frame

theorem frame_properties : FrameFacts := by
  intro Dall D D1 J J1 h
  have o := frame_orth J J1 h
  have o' := frame_orth' J J1 h
  refine ⟨o, o', frame_dim J J1 h, ?_, ?_, ?_, Wfr_uni J J1 h, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_conjTranspose]
  · have : J * Jᴴ * (J * Jᴴ) = J * (Jᴴ * J) * Jᴴ := by simp only [Matrix.mul_assoc]
    rw [this, h.1, Matrix.mul_one]
  · have : J * Jᴴ * (J1 * J1ᴴ) = J * (Jᴴ * J1) * J1ᴴ := by simp only [Matrix.mul_assoc]
    rw [this, o, Matrix.mul_zero, Matrix.zero_mul]
  · rw [Wfr_mul, rows_mul_WfrH]
    have a1 : Jᴴ * (J * Jᴴ) = Jᴴ := by rw [← Matrix.mul_assoc, h.1, Matrix.one_mul]
    have a2 : J1ᴴ * (J * Jᴴ) = 0 := by rw [← Matrix.mul_assoc, o', Matrix.zero_mul]
    rw [a1, a2, h.1, o, Matrix.zero_mul, Matrix.zero_mul]

lemma isUni_one (n : ℕ) : IsUni (1 : Matrix (Fin n) (Fin n) ℂ) := ⟨by simp, by simp⟩

lemma Brow_eq {ι : Type} {D D' : ℕ} {d : ι → ℕ} (W : Matrix (Fin D') (Fin D) ℂ)
    (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) :
    Brow W B = Btwist B (fun _ => 1) W (fun _ => 1) := by
  funext u; simp [Brow, Btwist]

theorem block_matrix_decomposition : RowsBlock := by
  intro ι _ Dall D D1 d B ga J J1 h
  obtain ⟨-, i1, i2, i3⟩ := twist_invariance ι Dall (D + D1) d B ga (fun _ => 1) (Wfr J J1)
    (fun _ => 1) (fun _ => one_ne_zero) (Wfr_uni J J1 h) (fun _ => isUni_one _)
  rw [gaTw_one, ← Brow_eq] at i1 i2 i3
  refine ⟨fun u k j => ?_, fun u k j => ?_, i1, i2, i3⟩
  · unfold Brow; rw [Wfr_mul]; simp
  · unfold Brow; rw [Wfr_mul]; simp

theorem corollary_transport : CorTransport := by
  intro ι _ Dall D D1 d P ga c V U J J1 A Y' Y η e del hga hc hV hU hJ hdel hD hMI hF1 hF2
  obtain ⟨g1, i1, i2, -⟩ := twist_invariance ι Dall Dall d P ga c V U hc hV hU
  obtain ⟨r1, -, j1, j2, -⟩ := block_matrix_decomposition ι Dall D D1 d (Btwist P c V U) (gaTw ga c) J J1 hJ
  have hdim : ((D + D1 : ℕ) : ℝ) = (Dall : ℝ) := by rw [frame_dim J J1 hJ]
  refine ⟨fun u => (g1 u).mpr (hga u), fun u k j => ?_, (j1 η).mpr ((i1 η).mpr hF1),
    (j2 e).mpr ((i2 e).mpr hF2), by rw [hdim]; exact hD, ?_⟩
  · rw [r1, hMI u]
    unfold Btwist
    rw [Matrix.mul_smul]
  · rw [hdim]; exact (block_count_valid Dall D del hdel).mp hD

lemma card_mul_le {ι : Type} [Fintype ι] (d : ι → ℕ) (t : ℝ) (h : ∀ u, t ≤ (d u : ℝ)) :
    (Fintype.card ι : ℝ) * t ≤ Rs d := by
  unfold Rs
  calc (Fintype.card ι : ℝ) * t = ∑ _u : ι, t := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun u _ => h u

theorem wordCount_valid : WordCount := by
  intro ι _ d C0 Gam sg Dstar hC hG hs hD hcard hd
  have h1 : C0 * Gam ^ 2 / sg ≤ (Fintype.card ι : ℝ) := by rw [hcard]; exact Nat.le_ceil _
  have h2 := card_mul_le d _ hd
  have h3 : Dstar / sg = (C0 * Gam ^ 2 / sg) * (Dstar / Gam ^ 2 / C0) := by field_simp
  rw [h3]
  exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) h2

theorem word_log_real : WordLogReal := by
  intro k X hX h
  have h2 : Real.log ((2 : ℝ) ^ (k - 3)) = (k - 3) * Real.log 2 := Real.log_rpow (by norm_num) _
  rw [← h2]
  rcases Nat.eq_zero_or_pos ⌈X⌉₊ with h0 | h0
  · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
    exact Real.log_nonneg (by linarith)
  · exact Real.log_le_log (by exact_mod_cast h0) ((Nat.ceil_lt_add_one hX).le.trans h)

theorem corollary_chain : CorChain := by
  intro ι _ Dall D D1 d r Pf Vr ga c V U J J1 A Y' Y Dstar sg η0 η1 e0 de del C0 Gam h
  obtain ⟨hga, hDs, hs, hs20, hC, hG, hcard, hd, a1, a2, a3, a4, a5, hS, hVr, hde0, hde, hcor, hc,
    hV, hU, hJ, hdel, hD, -, -, hMI⟩ := h
  have hR := wordCount_valid ι d C0 Gam sg Dstar hC hG hs hDs.le hcard hd
  have f1 := compressTraceSquareBound ι Dall d r Pf Vr ga Dstar sg η0 η1 e0 de hVr (fun u => (hga u).le) hDs hs
    hs20 hR a1 a2 a3 a4 a5 hde0 hde hcor hS
  obtain ⟨fR, f2⟩ := compressDiagDefectBound ι Dall d r Pf Vr ga de e0 hVr (by linarith) a4 hS.2.1 hcor
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := corollary_transport ι Dall D D1 r (Bram Pf Vr) ga c V U J J1 A
    Y' Y _ _ del hga hc hV hU hJ hdel hD hMI f1 f2
  have he : 2 * e0 ≤ 1 / 4 := by
    have hsq : Real.sqrt e0 ^ 2 = e0 := Real.sq_sqrt a4
    have h0 := Real.sqrt_nonneg e0
    nlinarith
  have hRd : 0 < Rs d := lt_of_lt_of_le (div_pos hDs hs) hR
  have hDall : 0 < Dall := by
    rcases Nat.eq_zero_or_pos Dall with h0 | h0
    · exfalso
      subst h0
      have hz : ∀ u, (d u : ℝ) ≤ 0 := by
        intro u
        have hK : Kd Pf ga u = 0 := by
          unfold Kd Kp
          have : (Pf u)ᴴ * Pf u = 0 := by ext i j; simp [Matrix.mul_apply]
          rw [this, smul_zero]
        have h1 := hS.2.1 u
        have h2 : hsSq (0 - 1 : Matrix (Fin (d u)) (Fin (d u)) ℂ) = (d u : ℝ) := by
          rw [← hsSq_one (d u)]; simp [hsSq]
        rw [hK, h2] at h1
        have h3 : (0 : ℝ) ≤ (d u : ℝ) := Nat.cast_nonneg _
        nlinarith
      have : Rs d ≤ 0 := by
        unfold Rs; exact Finset.sum_nonpos fun u _ => hz u
      linarith
    · exact h0
  refine ⟨c1, c2, c3, c4, he, c5, c6, ?_, ?_, by linarith, hDall, ?_⟩
  · have h3 : 0 < (1 - de) * Rs d := mul_pos (by linarith) hRd
    linarith
  · have := Real.sqrt_nonneg de
    linarith
  · have h1 : (D : ℝ) ≤ (Dall : ℝ) := by
      rw [frame_dim J J1 hJ]; push_cast
      have : (0 : ℝ) ≤ (D1 : ℝ) := Nat.cast_nonneg _
      linarith
    have h2 : (0 : ℝ) < (Dall : ℝ) := by exact_mod_cast hDall
    by_contra hneg
    rw [not_le] at hneg
    nlinarith

namespace Model

def J0 : Matrix (Fin 2) (Fin 1) ℂ := !![1; 0]
def modelEmbedding : Matrix (Fin 2) (Fin 1) ℂ := !![0; 1]
def c0 : Fin 20 → ℂ := fun _ => 2 * Complex.I
def P0 : ∀ _u : Fin 20, Matrix (Fin 2) (Fin 2) ℂ := fun _ => 1
def r0 : Fin 20 → ℕ := fun u => if u = 0 then 1 else 2
def En (n : ℕ) : Matrix (Fin 2) (Fin n) ℂ := fun i j => if i.val = j.val then 1 else 0
def V0 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def U0 : ∀ u : Fin 20, Matrix (Fin (r0 u)) (Fin (r0 u)) ℂ := fun _ => Complex.I • 1

lemma frame0 : OrthFrame J0 modelEmbedding := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [J0, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i; fin_cases j; simp [modelEmbedding, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [J0, modelEmbedding, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]

lemma hs_one : hsSq (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
  simp [hsSq, Fin.sum_univ_two, Matrix.one_apply]; norm_num

lemma kp0 (u u' : Fin 20) : Kp (d := fun _ => 2) P0 (fun _ => (1 : ℝ)) u u' = 1 := by
  simp [Kp, P0]

lemma en_isom (n : ℕ) (hn : n = 1 ∨ n = 2) : (En n)ᴴ * En n = 1 := by
  rcases hn with rfl | rfl
  · ext i j; fin_cases i; fin_cases j; simp [En, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [En, Matrix.mul_apply]

lemma model_rank_one_or_two (u : Fin 20) : r0 u = 1 ∨ r0 u = 2 := by
  unfold r0; split_ifs <;> simp

lemma model_unitary : IsUni V0 := by
  constructor <;>
  · ext i j; fin_cases i <;> fin_cases j <;> simp [V0, Matrix.mul_apply, Fin.sum_univ_two]

lemma model_unitary_entries (u : Fin 20) : IsUni (U0 u) := by
  constructor <;> simp [U0, Matrix.conjTranspose_smul, smul_smul]

def A0 : ∀ u, Matrix (Fin 1) (Fin (r0 u)) ℂ :=
  fun u => c0 u • (J0ᴴ * (V0 * Bram (d := fun _ => 2) (r := r0) P0 (fun u => En (r0 u)) u * U0 u))

theorem hyp0 :
    ChainHyp (d := fun _ => 2) (r := r0) P0 (fun u => En (r0 u)) (fun _ => 1) c0 V0 U0 J0 modelEmbedding A0 1
      (fun _ => 1) 2 (1 / 20) 0 0 0 (1 / 40) (1 / 2) 1 1 := by
  refine ⟨fun _ => by norm_num, by norm_num, by norm_num, le_refl _, by norm_num, by norm_num, ?_,
      fun _ => by norm_num, by norm_num, by norm_num, by norm_num, le_refl _,
      by rw [Real.sqrt_zero]; norm_num, ?_, ?_,
      by norm_num, by norm_num, ?_, ?_, model_unitary, model_unitary_entries, frame0, by norm_num, by norm_num, by simp,
      fun _ => by simp, fun u => by simp [A0]⟩
  · have : (1 : ℝ) * 1 ^ 2 / (1 / 20) = ((20 : ℕ) : ℝ) := by norm_num
    rw [this, Nat.ceil_natCast]; simp
  · refine ⟨fun u u' _ => ?_, fun u => ?_, by norm_num⟩
    · rw [kp0, hs_one]; norm_num
    · have : Kd (d := fun _ => 2) P0 (fun _ => (1 : ℝ)) u = 1 := kp0 u u
      rw [this]; simp [hsSq]
  · intro u; exact en_isom _ (model_rank_one_or_two u)
  · have h : ∀ u : Fin 20, (((2 : ℕ) : ℝ) - (r0 u : ℝ)) = if u = 0 then 1 else 0 := by
      intro u; unfold r0; split_ifs <;> norm_num
    simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [Rs]; norm_num
  · intro u; simp [c0]

end Model

theorem twist_ramified_factor : TwRamFactor := by
  intro ι _ Dall D' d r Pf Vr ga c V U W hc hV hU hW hVr
  refine ⟨fun u => ?_, fun u => ?_, fun Dstar η0 η1 e0 => ?_⟩
  · unfold Brow Btwist Bram VrS
    simp only [Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  · unfold VrS
    rw [conjTranspose_mul]
    have : (U u)ᴴ * (Vr u)ᴴ * (Vr u * U u) = (U u)ᴴ * ((Vr u)ᴴ * Vr u) * U u := by
      simp only [Matrix.mul_assoc]
    rw [this, hVr u, Matrix.mul_one, (hU u).1]
  · obtain ⟨-, -, -, i3⟩ := twist_invariance ι Dall Dall d Pf ga c V (fun _ => 1) hc hV
      (fun _ => isUni_one _)
    obtain ⟨-, -, -, j3⟩ := twist_invariance ι Dall D' d (Btwist Pf c V (fun _ => 1)) (gaTw ga c)
      (fun _ => 1) W (fun _ => 1) (fun _ => one_ne_zero) hW (fun _ => isUni_one _)
    rw [gaTw_one, ← Brow_eq] at j3
    exact (j3 _ _ _ _).trans (i3 _ _ _ _)

lemma WfrS_isom {Dall D D1 : ℕ} (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (h : OrthFrame J J1) : (WfrS J J1)ᴴ * WfrS J J1 = 1 := by
  unfold WfrS
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_conjTranspose,
    conjTranspose_conjTranspose, Matrix.fromCols_mul_fromRows, h.2.2]

lemma KpG_BfS {ι : Type} [Fintype ι] {Dall D D1 : ℕ} {d : ι → ℕ}
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) (h : OrthFrame J J1)
    (g : ι → ℝ) (u u' : ι) :
    MatrixLatticeEstimates.KpG (BfS Pf c V J J1) g u u' = Kp (Btwist Pf c V (fun _ => 1)) g u u' := by
  unfold MatrixLatticeEstimates.KpG Kp BfS Btwist
  have key : (WfrS J J1 * (V * Pf u))ᴴ * (WfrS J J1 * (V * Pf u')) = (V * Pf u)ᴴ * (V * Pf u') := by
    rw [conjTranspose_mul]
    have : (V * Pf u)ᴴ * (WfrS J J1)ᴴ * (WfrS J J1 * (V * Pf u'))
        = (V * Pf u)ᴴ * ((WfrS J J1)ᴴ * WfrS J J1) * (V * Pf u') := by
      simp only [Matrix.mul_assoc]
    rw [this, WfrS_isom J J1 h, Matrix.mul_one]
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, key]

theorem chain_substitution : ChainCondition := by
  intro ι _ Dall D D1 d r Pf Vr ga c V U J J1 A Y' Y Dstar sg η0 η1 e0 de del C0 Gam h
  obtain ⟨c1, c2, -, -, -, c5, -, c7, -, -, -, c11⟩ :=
    corollary_chain ι Dall D D1 d r Pf Vr ga c V U J J1 A Y' Y Dstar sg η0 η1 e0 de del C0 Gam h
  obtain ⟨hga, hDs, hs, hs20, hC, hG, hcard, hd, a1, a2, a3, a4, a5, hS, hVr, hde0, hde, hcor, hc,
    hV, hU, hJ, hdel, hD, -, -, hMI⟩ := h
  have hR := wordCount_valid ι d C0 Gam sg Dstar hC hG hs hDs.le hcard hd
  obtain ⟨-, t2, -⟩ := twist_ramified_factor ι Dall (D + D1) d r Pf Vr ga c V U (Wfr J J1) hc hV hU
    (Wfr_uni J J1 hJ) hVr
  obtain ⟨-, -, -, i3⟩ := twist_invariance ι Dall Dall d Pf ga c V (fun _ => 1) hc hV
    (fun _ => isUni_one _)
  have hRs : MatrixLatticeEstimates.RsG (fun u => Fin (d u)) = Rs d := by simp [MatrixLatticeEstimates.RsG, Rs]
  have hrel : ∀ u i j, (BfS Pf c V J J1 u * VrS Vr U u) i j
      = Brow (Wfr J J1) (Btwist (Bram Pf Vr) c V U) u (finSumFinEquiv i) j := by
    intro u i j
    have e1 : BfS Pf c V J J1 u * VrS Vr U u
        = Matrix.fromRows Jᴴ J1ᴴ * Btwist (Bram Pf Vr) c V U u := by
      unfold BfS VrS WfrS Btwist Bram
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    unfold Brow
    rw [e1, Wfr_mul, ← Matrix.fromRows_mul]
    simp
  refine ⟨c1, t2, by rw [hRs]; exact hR, by simpa only [Fintype.card_fin, hRs] using hcor, ?_,
    fun u k j => ?_, hrel, ?_, c11, hdel, ?_⟩
  · have hS' := (i3 Dstar η0 η1 e0).mpr hS
    refine ⟨fun u u' hne => ?_, fun u => ?_, ?_⟩
    · rw [KpG_BfS Pf c V J J1 hJ]
      simpa only [Fintype.card_fin] using hS'.1 u u' hne
    · unfold MatrixLatticeEstimates.KdG
      rw [KpG_BfS Pf c V J J1 hJ]
      have h1 := hS'.2.1 u
      unfold Kd at h1
      simpa only [Fintype.card_fin] using h1
    · have : (Fintype.card (Fin D ⊕ Fin D1) : ℝ) = (Dall : ℝ) := by
        rw [frame_dim J J1 hJ]; simp
      rw [this]; exact hS'.2.2
  · rw [hrel, finSumFinEquiv_apply_left]
    exact c2 u k j
  · have : ((∑ u, Fintype.card (Fin (r u)) : ℕ) : ℝ) = Rs r := by simp [Rs]
    have h2 : (0 : ℝ) < ((∑ u, Fintype.card (Fin (r u)) : ℕ) : ℝ) := by rw [this]; exact c7
    exact_mod_cast h2
  · simpa using c5

namespace Model

section Lat

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

def bW : Basis (Fin 1) K K := Basis.singleton (Fin 1) K
def bV (i : Fin 20) : Basis (Fin (r0 i)) K (Fin (r0 i) → K) := Pi.basisFun K (Fin (r0 i))
def Lc : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}
def LN (i : Fin 20) : Submodule (𝓞 K) (Fin (r0 i) → K) :=
  Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin (r0 i))))
def MB (i : Fin 20) : Matrix (Fin 1) (Fin (r0 i)) K := fun _ j => if j.val = 1 then -2 else 0
def BB (i : Fin 20) : (Fin (r0 i) → K) →ₗ[K] K := Matrix.toLin (bV K i) (bW K) (MB K i)

end Lat

end Model

end

end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
