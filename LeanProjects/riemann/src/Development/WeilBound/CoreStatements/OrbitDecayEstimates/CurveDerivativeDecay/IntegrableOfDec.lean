import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.KFiniteWordBoundIndefUnitary
import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.OneLeHsG
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay

noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

def nG {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : ℝ := Real.sqrt (hs (uMat g))

theorem nG_mul {m : ℕ} {ε : Fin m → Bool} (g h : UJ ε) : nG (g * h) ≤ nG g * nG h := sqrt_frobenius_mul_le _ _

theorem one_le_nG {m : ℕ} (hm : 1 ≤ m) {ε : Fin m → Bool} (g : UJ ε) : 1 ≤ nG g :=
  Real.one_le_sqrt.2 (one_le_hsG hm g)

theorem nG_sq {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : nG g ^ 2 = hs (uMat g) :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)

theorem uMat_inv {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : uMat g⁻¹ = Jm ε * (uMat g)ᴴ * Jm ε := by
  have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
  have e : uMat g * uMat g⁻¹ = 1 := determinant_character_mul_inv g
  calc uMat g⁻¹ = Jm ε * Jm ε * uMat g⁻¹ := by rw [Jm_mul_self, Matrix.one_mul]
    _ = Jm ε * ((uMat g)ᴴ * Jm ε * uMat g) * uMat g⁻¹ := by rw [hg]
    _ = Jm ε * (uMat g)ᴴ * Jm ε * (uMat g * uMat g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [e, Matrix.mul_one]

theorem hs_conjJ {m : ℕ} (ε : Fin m → Bool) (M : Matrix (Fin m) (Fin m) ℂ) : hs (Jm ε * Mᴴ * Jm ε) = hs M := by
  unfold hs
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, norm_mul, norm_star]
  split_ifs <;> simp

theorem nG_inv {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : nG g⁻¹ = nG g := by
  unfold nG
  rw [uMat_inv, hs_conjJ]

theorem hs_inv_sub_one {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : hs (uMat g⁻¹ - 1) = hs (uMat g - 1) := by
  rw [← hs_conjJ ε (uMat g - 1), uMat_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Jm_mul_self]

theorem hs_of_compact {m : ℕ} {ε : Fin m → Bool} (hc : ∀ a b, ε a = ε b) (g : UJ ε) : hs (uMat g) = m := by
  have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
  unfold hs
  rw [Finset.sum_comm]
  have : ∀ j, ∑ i, ‖uMat g i j‖ ^ 2 = 1 := by
    intro j
    have h1 := congrFun (congrFun hg j) j
    simp only [Jm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    have h2 : ∀ i, (if ε i = true then star (uMat g i j) * 1 else star (uMat g i j) * -1) * uMat g i j =
        (if ε j = true then 1 else -1) * ((‖uMat g i j‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      have := Complex.conj_mul' (uMat g i j)
      rw [hc i j]
      split_ifs <;> simp [← this]
    simp only [h2, ← Finset.mul_sum] at h1
    have h3 : (∑ i, ((‖uMat g i j‖ ^ 2 : ℝ) : ℂ)) = 1 := by
      split_ifs at h1
      · simpa using h1
      · linear_combination -h1
    exact_mod_cast h3
  simp [this]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem dec_low {m N : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hm : 1 ≤ m)
    (hmN : m ≤ N) (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hDS : IsDS ε lam π)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (N : ℝ) ^ 3)) {v : H} (hv : v ∈ lowKSub ε lam π) (hv1 : ‖v‖ = 1)
    {A : ℕ} (hA1 : 1 ≤ A) (hA : A ≤ 12 * N ^ 2) (g : UJ ε) :
    ‖⟪v, π (uMat g) v⟫_ℂ‖ ≤ (Real.exp 1 * Real.sqrt m) ^ A * (nG g)⁻¹ ^ A := by
  have : CompleteSpace H := hDS.1
  have hm2 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN2 : (m : ℝ) ≤ N := by exact_mod_cast hmN
  by_cases hcp : ∀ a b, ε a = ε b
  · have h1 := norm_inner_le_norm (𝕜 := ℂ) v (π (uMat g) v)
    rw [hDS.2.2.1.2.1 _ g.2, hv1, one_mul] at h1
    have h2 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by linarith)
    unfold nG
    rw [hs_of_compact hcp, ← mul_pow, mul_assoc, mul_inv_cancel₀ h2.ne', mul_one]
    exact h1.trans (one_le_pow₀ (Real.one_le_exp zero_le_one))
  have hpq' : (∃ a, ε a = true) ∧ ∃ a, ε a = false := by
    push_neg at hcp
    obtain ⟨a, b, hab⟩ := hcp
    cases ha : ε a <;> cases hb : ε b <;> simp_all <;> exact ⟨⟨_, ‹_›⟩, ⟨_, ‹_›⟩⟩
  obtain ⟨hp, hq⟩ := hpq'
  set h : ℝ := 200 * (N : ℝ) ^ 3 with hh
  have hN3 : (m : ℝ) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ (by linarith) hN2 3
  have hm3 : (1 : ℝ) ≤ m ^ 3 := one_le_pow₀ hm2
  have hpm : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ m := by
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)
  have hqm : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ m := by
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)
  have hq1 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := by
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact le_min (Finset.card_pos.2 ⟨a, by simp [ha]⟩) (Finset.card_pos.2 ⟨b, by simp [hb]⟩)
  have hq0 : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ m := le_trans (by exact_mod_cast min_le_left _ _) hpm
  have hq1' : (1 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := by exact_mod_cast hq1
  have hmm : (m : ℝ) ^ 2 ≤ m ^ 3 := by nlinarith
  have hpq : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ m * m :=
    mul_le_mul hpm hqm (Nat.cast_nonneg _) (by linarith)
  obtain ⟨k, X, hX, e⟩ := ReciprocityTheory.ChartRestriction.DS.S7.polar_exists (ε := ε) (g := uMat g) g.2
  have hd := ReciprocityTheory.ChartRestriction.DS.coef_dec_of_isDS hDS hl hg hq1 (by nlinarith) (by nlinarith) ⟨hv1, hv⟩ k hX
  rw [← e] at hd
  set c := Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) with hc
  have hc1 : 1 ≤ c := Real.one_le_sqrt.2 (by linarith)
  have hcm : c ≤ 2 * N := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  set s := Real.sqrt (ReciprocityTheory.ChartRestriction.DS.S7.hs X) with hs_def
  have hsX : ReciprocityTheory.ChartRestriction.DS.S7.hs X = s ^ 2 := (Real.sq_sqrt (ReciprocityTheory.ChartRestriction.DS.S7.hs_nonnegVG X)).symm
  have hG1 := one_le_nG hm g
  have hN : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hGle : nG g ≤ Real.sqrt m * Real.exp s := by
    unfold nG
    rw [e]
    change Real.sqrt (ReciprocityTheory.ChartRestriction.DS.S7.hs _) ≤ _
    rw [ReciprocityTheory.ChartRestriction.DS.S7.hs_kmulVG, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have e2 : Real.exp s ^ 2 = Real.exp (2 * s) := by rw [← Real.exp_nat_mul]; norm_num
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), e2]
    exact ReciprocityTheory.ChartRestriction.DS.S7.hs_exp_leVG X
  have hA' : (A : ℝ) ≤ 12 * N ^ 2 := by exact_mod_cast hA
  have hA1' : (1 : ℝ) ≤ A := by exact_mod_cast hA1
  have hr := ReciprocityTheory.ChartRestriction.DS.sigZeroDecay_real (h := 8 * c * A) (s := s) (by positivity) hc1 hN (by linarith) hGle
  rw [show 8 * c * A / (8 * c) = (A : ℝ) by field_simp, Real.rpow_neg (by linarith), Real.rpow_natCast,
    Real.rpow_natCast, ← inv_pow] at hr
  rw [hsX] at hd
  have hmin : 0 ≤ min (s ^ 2) (s / c) := le_min (by positivity) (by positivity)
  have hle : 8 * c * A ≤ h := by
    have : c * A ≤ (2 * N) * (12 * N ^ 2) := mul_le_mul hcm hA' (by linarith) (by linarith)
    nlinarith
  refine hd.trans ((Real.exp_le_exp.2 (by nlinarith)).trans (hr.trans (le_of_eq ?_)))
  rw [show Real.exp (A : ℝ) = Real.exp 1 ^ A by rw [← Real.exp_nat_mul, mul_one], ← mul_pow]

theorem dec_conj {m : ℕ} {ε : Fin m → Bool} {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hm : 1 ≤ m)
    (hπ : IsURepOn (UJset ε) π) {v : H} {C : ℝ} (hC : 0 ≤ C) {A : ℕ}
    (hd : ∀ g : UJ ε, ‖⟪v, π (uMat g) v⟫_ℂ‖ ≤ C * (nG g)⁻¹ ^ A) (g₀ g : UJ ε) :
    ‖⟪π (uMat g₀) v, π (uMat g) (π (uMat g₀) v)⟫_ℂ‖ ≤ C * hs (uMat g₀) ^ A * (nG g)⁻¹ ^ A := by
  let U : H →ₗᵢ[ℂ] H := ⟨(π (uMat g₀)).toLinearMap, hπ.2.1 _ g₀.2⟩
  have e : π (uMat g) (π (uMat g₀) v) = π (uMat g₀) (π (uMat (g₀⁻¹ * g * g₀)) v) := by
    have h1 := hπ.1.2 (uMat g) g.2 (uMat g₀) g₀.2
    have h2 := hπ.1.2 (uMat g₀) g₀.2 (uMat (g₀⁻¹ * g * g₀)) (g₀⁻¹ * g * g₀).2
    have h3 : uMat g₀ * uMat (g₀⁻¹ * g * g₀) = uMat g * uMat g₀ := by
      change uMat (g₀ * (g₀⁻¹ * g * g₀)) = uMat (g * g₀)
      congr 1
      group
    rw [← ContinuousLinearMap.comp_apply, ← h1, ← h3, h2, ContinuousLinearMap.comp_apply]
  have e2 := U.inner_map_map v (π (uMat (g₀⁻¹ * g * g₀)) v)
  rw [e]
  change ‖⟪U v, U _⟫_ℂ‖ ≤ _
  rw [e2]
  refine (hd _).trans ?_
  rw [mul_assoc C, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold nG; positivity) ?_ A) hC
  have h1 : nG g ≤ nG g₀ * nG (g₀⁻¹ * g * g₀) * nG g₀ := by
    calc nG g = nG (g₀ * (g₀⁻¹ * g * g₀) * g₀⁻¹) := by congr 1; group
      _ ≤ nG (g₀ * (g₀⁻¹ * g * g₀)) * nG g₀⁻¹ := nG_mul _ _
      _ ≤ _ := by rw [nG_inv]; exact mul_le_mul_of_nonneg_right (nG_mul _ _) (by unfold nG; positivity)
  have h2 := one_le_nG hm g
  have h3 := one_le_nG hm (g₀⁻¹ * g * g₀)
  rw [← nG_sq, ← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_le_iff₀ (by linarith)]
  nlinarith

theorem nearSet_lt_top {m : ℕ} (ε : Fin m → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] : μ (nearSet ε 1) < ⊤ := by
  have hc : IsCompact {g : UJ ε | hsG g ≤ (Real.sqrt m + 1) ^ 2} := by
    have := (isClosedEmbeddingMatrix m ε).1.isCompact_preimage ((hermitian_small_ball m ε).1 ((Real.sqrt m + 1) ^ 2))
    convert this using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hsG]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  refine (measure_mono fun g hg => ?_).trans_lt hc.measure_lt_top
  have h1 := sqrt_frobenius_add_le (1 : Matrix (Fin m) (Fin m) ℂ) (coeMatrixAlt ε g - 1)
  rw [add_sub_cancel, f1auxiliary_hs_one] at h1
  have h2 : Real.sqrt (hs (coeMatrixAlt ε g - 1)) ≤ 1 := Real.sqrt_le_iff.2 ⟨zero_le_one, hg⟩
  show hs (coeMatrixAlt ε g) ≤ _
  rw [← Real.sqrt_le_left (by positivity)]
  linarith

theorem integrable_of_dec {m : ℕ} {ε : Fin m → Bool} (hm : 1 ≤ m) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] {f : UJ ε → ℂ}
    (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C) {A : ℕ} (hA : 2 * m ^ 2 + 1 ≤ A) (hd : ∀ g, ‖f g‖ ≤ C * (nG g)⁻¹ ^ A) :
    Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have h1 := int_ratio hm ε μ one_pos (by norm_num) hA
  calc ∫⁻ g, ‖f g‖ₑ ∂μ ≤ ∫⁻ g, ENNReal.ofReal C * ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ∂μ := by
        refine lintegral_mono fun g => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hd g)
    _ = ENNReal.ofReal C * ∫⁻ g, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (nearSet_lt_top ε μ)))

end CompanionTheory.Lime.T3
