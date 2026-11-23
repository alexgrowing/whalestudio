import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DyadicSummationWithDecayStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramNumberMulLeadingMinorLeTwoPowStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymmStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoSidedSizeFunctionPosInvariantContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationDegenerateSidePieceBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorsGramNumberLeMajorantLengthsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagGramNumberNormalizedIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableAndNormAmplitudeLeOfPairingsStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.DegConv

variable {k r : ℕ}

theorem continuous_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem lmul_inv_lmul {γ : Mat k r} (hγ : γ ∈ GG k r) (x : Mt k r) : lmulM γ⁻¹ (lmulM γ x) = x :=
  Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ)

def lmulEquiv {γ : Mat k r} (hγ : γ ∈ GG k r) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM γ
  invFun := lmulM γ⁻¹
  left_inv := lmul_inv_lmul hγ
  right_inv x := Matrix.mul_nonsing_inv_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ)
  measurable_toFun := (continuous_lmul γ).measurable
  measurable_invFun := (continuous_lmul γ⁻¹).measurable

theorem quot_map {γ : Mat k r} (hγ : γ ∈ GG k r) {μG μR ν : Measure (Mt k r)} (hG : IsHaarOn (GG k r) μG)
    (h : IsQuotMeas μG μR ν) : IsQuotMeas μG (μR.map (conjM γ)) (ν.map (lmulEquiv hγ)) := by
  intro f hf
  rw [lintegral_map_equiv]
  have h1 := h (fun x => f (lmulM γ x)) (hf.comp (continuous_lmul γ).measurable)
  rw [← lintegral_map hf (continuous_lmul γ).measurable, hG.2.2.2 γ hγ] at h1
  rw [h1]
  refine lintegral_congr fun x => ?_
  have hm : Measurable fun s : Mt k r => f (rmulM (Matrix.of (lmulEquiv hγ x)) s) :=
    hf.comp (continuous_rmulM _).measurable
  refine Eq.trans ?_ (lintegral_map hm (continuous_conj γ).measurable).symm
  refine lintegral_congr fun s => ?_
  congr 1
  show γ * (Matrix.of s * Matrix.of x) = γ * Matrix.of s * γ⁻¹ * (γ * Matrix.of x)
  rw [Matrix.mul_assoc _ γ⁻¹, Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ),
    Matrix.mul_assoc]

def Gs (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ GG k r}

def ext0 (f : Mat k r → ℝ) : Mt k r → ℝ := Set.indicator (Gs k r) fun x => f (Matrix.of x)

theorem cochainExtendByZeroSubgroup_of_mem (f : Mat k r → ℝ) {x : Mt k r} (hx : Matrix.of x ∈ GG k r) : ext0 f x = f (Matrix.of x) :=
  Set.indicator_of_mem (s := Gs k r) hx _

theorem amplifierAbsConvExtendByZero_of_not_mem (f : Mat k r → ℝ) {x : Mt k r} (hx : Matrix.of x ∉ GG k r) : ext0 f x = 0 :=
  Set.indicator_of_notMem (s := Gs k r) hx _

theorem measurable_amplifierAbsConvExtendByZero {f : Mat k r → ℝ} (hf : ContinuousOn f (GG k r)) : Measurable (ext0 f) := by
  classical
  have hc : IsClosed (Gs k r) := isClosedSub_GG.2.1
  have h1 : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) (Gs k r) := hf
  have := ContinuousOn.measurable_piecewise (g := fun _ => (0 : ℝ)) h1 continuousOn_const hc.measurableSet
  convert this using 1
  exact (Set.piecewise_eq_indicator).symm

def Kc (k r j : ℕ) (De : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (4 * r ^ 2) * De ^ (8 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) *
    4 ^ (k - 1 - j) * (4 * r + 4)

theorem side {j : ℕ} {hj : j ≤ r} {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {z z' : Fin (2 * r + k + 1) → ℂ} {π' : Mat k r → (Wq →L[ℂ] Wq)} {ψ' : Mat k r → ℂ}
    {μG μW' νS' μR νR : Measure (Mt k r)} {Φ' : Mat k r → Wq} {γ : Mat k r} {c κ s H₁ De : ℝ} {q : ℕ}
    (hj1 : 1 ≤ j) (hk : j + 2 ≤ k) (hκ : 0 < κ) (hs : 0 < s) (hH : 1 ≤ H₁) (hγ : γ ∈ GG k r)
    (h1 : OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c) (h2 : TailBd z' νS' Φ' q H₁)
    (h4 : DeOK k r z z' γ De) (h5 : IsNormalFormStabilizerMeasure k r hj z z' γ s μR) (h6 : IsQuotMeas μG μR νR)
    (w : Wq) (hw : ‖w‖ = 1) (i i' : ℕ) (y : ℝ) (hy : 0 < y) :
    ∫⁻ x in {x | ext0 (Sg2 k r z') x ≤ 2 ^ (i' + 1) * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ < ext0 (Sg2 k r z') x) ∧
        ext0 (Sg2 k r z) (lmulM γ x) ≤ 2 ^ (i + 1) * H₁ ∧ y < ext0 (Yj k r hj z z' γ) x ∧
        ext0 (Yj k r hj z z' γ) x ≤ 2 * y},
      ENNReal.ofReal (ext0 (fun g => ‖⟪w, Φ' g⟫_ℂ‖) x ^ 2) ∂νR ≤
    ENNReal.ofReal (κ / s * Kc k r j De * c * (2 ^ (i + i' + 1) * H₁) ^ (16 * r ^ 3) * y ^ (2 * (k - 1 - j)) *
      (((2 : ℝ) ^ i') ^ (2 * q))⁻¹) := by
  have hH0 : 0 ≤ H₁ := zero_le_one.trans hH
  have q1 : (2 : ℝ) ^ (i + 1) * H₁ ≤ 2 ^ (i + i' + 1) * H₁ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) hH0
  have q2 : (2 : ℝ) ^ (i' + 1) * H₁ ≤ 2 ^ (i + i' + 1) * H₁ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) hH0
  have hR : (1 : ℝ) ≤ 2 ^ (i + i' + 1) * H₁ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hH
  have key := (GlobalTheory.T.amplification_degenerate_side_piece_bound k r j hj z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De q hj1 hk hκ hs hH h1 h2 h4 h5 h6).2
    w hw i' _ y hR hy
  refine le_trans (lintegral_mono' (Measure.restrict_mono ?_ le_rfl) fun x => ?_) (key.trans (le_of_eq ?_))
  · rintro x ⟨a1, a2, a3, a4, a5⟩
    have hx : Matrix.of x ∈ GG k r := by
      by_contra hx
      rw [amplifierAbsConvExtendByZero_of_not_mem _ hx] at a4
      exact lt_asymm hy a4
    have hx' : Matrix.of (lmulM γ x) ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx
    rw [cochainExtendByZeroSubgroup_of_mem _ hx] at a1 a2 a4 a5
    rw [cochainExtendByZeroSubgroup_of_mem _ hx'] at a3
    exact ⟨⟨hx, a1.trans q2, a3.trans q1, a4, a5⟩, a2⟩
  · by_cases hx : Matrix.of x ∈ GG k r
    · simp only [cochainExtendByZeroSubgroup_of_mem _ hx, le_refl]
    · simp [amplifierAbsConvExtendByZero_of_not_mem _ hx]
  · congr 1
    unfold fibVol0 Kc
    generalize (2 : ℝ) ^ (i + i' + 1) * H₁ = R
    rw [mul_pow 2 y, pow_mul (2 : ℝ) 2, mul_pow (R ^ (2 * r)), ← pow_mul R,
      show 2 * r * (8 * r ^ 2) = 16 * r ^ 3 by ring]
    norm_num only
    ring

theorem max_bounds {r : ℕ} {M D De Y T : ℝ} (hD0 : 0 < D) (hD : D⁻¹ ≤ De) (hT : 0 ≤ T) (hT' : T ≤ M)
    (hY : Y ≤ T ^ r / D) : Y ≤ M ^ r * De := by
  have hM : 0 ≤ M := hT.trans hT'
  refine hY.trans ?_
  rw [div_eq_mul_inv]
  gcongr

theorem one_le_Sg (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : 1 ≤ Sg k r z x := by
  unfold Sg; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem one_le_sgV (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (H₁ : ℝ) : 1 ≤ sgV k r z z' γ H₁ := by
  unfold sgV; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem arith (k r j q : ℕ) {H₁ De D sg : ℝ} (hj : 1 ≤ j) (hH : 1 ≤ H₁) (hDe : 1 ≤ De) (hD : 0 < D) (hsg : 1 ≤ sg) :
    16 * Kc k r j De * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) * De ^ 2 * (2 ^ j / D) ^ (k - 1 - j) *
      sg ^ (-(((q : ℝ) - (16 * r ^ 3 : ℕ) - 4 * r - 1) / r)) ≤ degBd k r j q H₁ De D sg := by
  unfold degBd Kc
  generalize k - 1 - j = m
  have e : (((16 * r ^ 3 : ℕ) : ℝ)) = 16 * (r : ℝ) ^ 3 := by push_cast; ring
  rw [e]
  have hs0 : 0 ≤ sg ^ (-(((q : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r)) := Real.rpow_nonneg (zero_le_one.trans hsg) _
  generalize sg ^ (-(((q : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r)) = t at hs0
  have h8 : (4 : ℝ) ^ m * (2 ^ j) ^ m ≤ 8 ^ (j * m) := by
    have : (4 : ℝ) ^ m ≤ 4 ^ (j * m) := pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left m hj)
    rw [← pow_mul, show (8 : ℝ) = 4 * 2 by norm_num, mul_pow]
    gcongr
  have hP : 0 ≤ Real.pi * Real.exp 1 / (m : ℝ) := by positivity
  rw [show 8 * Real.pi * Real.exp 1 / (m : ℝ) = 8 * (Real.pi * Real.exp 1 / m) by ring, mul_pow (8 : ℝ), div_pow _ D,
    pow_add De]
  generalize Real.pi * Real.exp 1 / (m : ℝ) = P at hP ⊢
  have hH0 : 0 ≤ H₁ := zero_le_one.trans hH
  have hDe0 : 0 ≤ De := zero_le_one.trans hDe
  have hc : 0 ≤ 16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) *
      (De ^ (8 * r ^ 2) * De ^ 2) * P ^ (j * m) * (D ^ m)⁻¹ * t := by positivity
  have := mul_le_mul_of_nonneg_left h8 hc
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · rw [div_eq_mul_inv]
    generalize (2 * H₁) ^ (16 * r ^ 3 + 4 * r) = A
    generalize (4 * r : ℝ) ^ (4 * r ^ 2) = B
    generalize ((2 : ℝ) ^ j) ^ m = C
    ring
  · generalize (2 * H₁) ^ (16 * r ^ 3 + 4 * r) = A
    generalize (4 * r : ℝ) ^ (4 * r ^ 2) = B
    ring

theorem deg_core : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ ψ' : Mat k r → ℂ) (μG μW μW' νS νS' μR νR : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 16 * r ^ 3 + 4 * r + 2 ≤ q → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z π ψ μG μW (ENNReal.ofReal κ • lebN k r) νS Φ c → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z νS Φ q H₁ → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) νR ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ νR c Φ Φ' γ)‖ ≤ κ / s * degBd k r j q H₁ De (Dj k r hj z z' γ) (sgV k r z z' γ H₁) := by
  intro k r j hj z z' Wp _ _ _ Wq _ _ _ π π' ψ ψ' μG μW μW' νS νS' μR νR Φ Φ' γ c κ s H₁ De q hj1 hk hq hκ hs hH o1 o2
    m1 m2 de nr qm
  obtain ⟨hγ, -, -, -, nr', hD, hDD, hde⟩ := GlobalTheory.T.stabilizer_measure_normalisation_symm k r j hj z z' γ s μR hs nr
  have hr : 1 ≤ r := hj1.trans hj
  have hγ' : γ⁻¹ ∈ GG k r := isClosedSub_GG.2.2.2.2 _ hγ
  have hG : IsHaarOn (GG k r) μG := o1.2.2.2.2.2.1
  have hc : 0 < c := o1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have cΦ : ContinuousOn Φ (GG k r) := o1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have cΦ' : ContinuousOn Φ' (GG k r) := o2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have de' := hde De de
  have qm' := quot_map hγ hG qm
  have hDe : (Dj k r hj z z' γ)⁻¹ ≤ De := de.2 ⟨j, by omega⟩ hj (norm_ne_zero_iff.1 hD.ne')
  have hDe1 : 1 ≤ De := de.1
  have n1 := (GlobalTheory.T.amplification_degenerate_side_piece_bound k r j hj z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De q hj1 hk hκ hs hH o2 m2 de nr qm).1
  have n2 := (GlobalTheory.T.amplification_degenerate_side_piece_bound k r j hj z' z π ψ μG μW νS _ _ Φ γ⁻¹ c κ s H₁ De q hj1 hk hκ hs hH o1 m1 de' nr' qm').1
  rw [MeasurableEquiv.map_apply] at n2
  have a1 : ∀ᵐ x ∂νR, Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (Matrix.of x) ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 n1] with x hx
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not] using hx
  have a2 : ∀ᵐ x ∂νR, Yj k r hj z' z γ⁻¹ (γ * Matrix.of x) ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 n2] with x hx
    exact fun h => hx (Or.inr h)
  have n0 : νR {x | Matrix.of x ∉ GG k r} = 0 := measure_mono_null (fun x hx => Or.inl hx) n1
  have hkk : 1 ≤ k - 1 - j := by omega
  have hK : 0 < κ / s * Kc k r j De * c := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    have : (0 : ℝ) < ((k - 1 - j : ℕ) : ℝ) := by exact_mod_cast hkk
    unfold Kc
    positivity
  have hsg := one_le_sgV z z' γ H₁
  have me : Measurable (lmulM γ : Mt k r → Mt k r) := (continuous_lmul γ).measurable
  have g1 := GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z o1.1 o1.2.1
  have g2 := GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z' o2.1 o2.2.1
  have main := GlobalTheory.T.integrable_and_norm_amplitude_le_of_pairings k r νR Φ Φ' γ c (16 * (κ / s * Kc k r j De * c) * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) * De ^ 2 *
    (2 ^ j / Dj k r hj z z' γ) ^ (k - 1 - j) *
    sgV k r z z' γ H₁ ^ (-(((q : ℝ) - (16 * r ^ 3 : ℕ) - 4 * r - 1) / r))) hγ n0 cΦ cΦ' hc (by positivity) ?_
  · refine ⟨main.1, main.2.trans ?_⟩
    have := arith k r j q hj1 hH hDe1 hD hsg
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ κ / s))
    field_simp
  intro v w hv hw
  have mA : Measurable (ext0 fun g => ‖⟪v, Φ g⟫_ℂ‖) :=
    measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ).norm
  have mB : Measurable (ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) :=
    measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ').norm
  have mS : Measurable (ext0 (Sg2 k r z)) := measurable_amplifierAbsConvExtendByZero g1.2.2.1
  have mS' : Measurable (ext0 (Sg2 k r z')) := measurable_amplifierAbsConvExtendByZero g2.2.2.1
  have mY : Measurable (ext0 (Yj k r hj z' z γ⁻¹)) :=
    (GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z' z γ⁻¹ o2.1 o1.1 o2.2.1 o1.2.1 hγ').1
  have mY' : Measurable (ext0 (Yj k r hj z z' γ)) := (GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z z' γ o1.1 o2.1 o1.2.1 o2.2.1 hγ).1
  have dy := GlobalTheory.T.dyadic_summation_with_decay (Mt k r) νR (fun x => ext0 (fun g => ‖⟪v, Φ g⟫_ℂ‖) (lmulM γ x))
    (ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) (fun x => ext0 (Sg2 k r z) (lmulM γ x)) (ext0 (Sg2 k r z'))
    (fun x => ext0 (Yj k r hj z' z γ⁻¹) (lmulM γ x)) (ext0 (Yj k r hj z z' γ)) r j (k - 1 - j) (16 * r ^ 3) q H₁ De
    (Dj k r hj z z' γ) _ _ _
    (mA.comp me) mB (mS.comp me) mS' (mY.comp me) mY' hr hkk hq hH hDe1 hD hK hK hsg ?_ ?_
    (fun i i' y hy => side hj1 hk hκ hs hH hγ o2 m2 de nr qm w hw i i' y hy)
  · rw [Real.sqrt_mul_self hK.le] at dy
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) dy
    filter_upwards [a1] with x hx
    have hx' : Matrix.of (lmulM γ x) ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx.1
    rw [cochainExtendByZeroSubgroup_of_mem _ hx.1, cochainExtendByZeroSubgroup_of_mem _ hx']
    rfl
  · filter_upwards [a1, a2] with x hx hx2
    have hx' : γ * Matrix.of x ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx.1
    have e1 : ∀ f : Mat k r → ℝ, ext0 f (lmulM γ x) = f (γ * Matrix.of x) := fun f => cochainExtendByZeroSubgroup_of_mem f hx'
    simp only [e1, cochainExtendByZeroSubgroup_of_mem _ hx.1]
    obtain ⟨s1, t1, -⟩ := g1.2.2.2 (γ * Matrix.of x)
    obtain ⟨s2, t2, -⟩ := g2.2.2.2 (Matrix.of x)
    have u1 : 0 ≤ Sg k r z (γ * Matrix.of x) := zero_le_one.trans (one_le_Sg _ _)
    have u2 : 0 ≤ Sg k r z' (Matrix.of x) := zero_le_one.trans (one_le_Sg _ _)
    obtain ⟨b1, b2, b3, b4⟩ := GlobalTheory.T.leading_minors_gram_number_le_majorant_lengths k r j hj z z' γ o1.1 o2.1 hγ _ hx.1
    obtain ⟨-, b5, b6, -⟩ := GlobalTheory.T.leading_minors_gram_number_le_majorant_lengths k r j hj z' z γ⁻¹ o2.1 o1.1 hγ' _ hx'
    rw [Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ), hDD] at b6
    have pw : (Sg k r z' (Matrix.of x) * Sg k r z (γ * Matrix.of x)) ^ r ≤
        (Sg2 k r z (γ * Matrix.of x) * Sg2 k r z' (Matrix.of x)) ^ r := by
      rw [mul_comm]
      exact pow_le_pow_left₀ (mul_nonneg u1 u2) (mul_le_mul t1 t2 u2 (u1.trans t1)) _
    refine ⟨norm_nonneg _, norm_nonneg _, s1, s2, lt_of_le_of_ne b5 hx2.symm, lt_of_le_of_ne b2 hx.2.symm, ?_,
      (b1 ⟨j, by omega⟩).trans pw,
      max_bounds hD hDe u2 (t2.trans (le_max_right _ _)) b6,
      max_bounds hD hDe u1 (t1.trans (le_max_left _ _)) b3, ?_⟩
    · rw [mul_comm (Yj k r hj z' z γ⁻¹ _)]
      exact GlobalTheory.T.flagGramNumber_mul_leadingMinor_le_two_pow k r j hj z z' γ s μR nr _ hx.1
    · exact (b4 H₁ hH).trans (max_le_max le_rfl (div_le_div_of_nonneg_right pw (by positivity)))
  · intro i i' y hy
    have h := side hj1 hk hκ hs hH hγ' o1 m1 de' nr' qm' v hv i' i y hy
    rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, add_comm i' i] at h
    refine le_trans (le_of_eq ?_) h
    congr 2
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [show lmulEquiv hγ x = lmulM γ x from rfl, lmul_inv_lmul hγ]

end GlobalTheory.Amp.DegConv
