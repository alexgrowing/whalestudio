import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.DerivativeUpperBound

noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

open ReciprocityTheory.ChartRestriction.DS (smD smE actM)

theorem exists_onePar {m : ℕ} {η : Fin m → Bool} {X : Matrix (Fin m) (Fin m) ℂ} (hX : inG η X) :
    ∃ c : ℝ → UJ η, (∀ s, uMat (c s) = NormedSpace.exp ((s : ℂ) • X)) ∧ c 0 = 1 ∧ ∀ s t, c (s + t) = c s * c t := by
  have : ∀ s : ℝ, ∃ u : UJ η, uMat u = NormedSpace.exp ((s : ℂ) • X) := fun s => by
    have h : NormedSpace.exp ((s : ℂ) • X) ∈ Set.range fun g : UJ η => uMat g := by
      rw [(isClosedEmbeddingMatrix m η).2]; exact exp_indefinite_unitary_holds m η X hX s
    exact h
  choose c hc using this
  refine ⟨c, hc, Subtype.ext (Units.ext ?_), fun s t => Subtype.ext (Units.ext ?_)⟩
  · change uMat (c 0) = 1
    rw [hc]; simp
  · change uMat (c (s + t)) = uMat (c s) * uMat (c t)
    rw [hc, hc, hc, one_parameter_subgroup_holds]

variable {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}

def embL (e : Fin n ⊕ Unit ≃ Fin (n + 1)) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ where
  toFun h := Matrix.reindex e e (Matrix.fromBlocks h 0 0 0)
  map_add' a b := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp
  map_smul' c a := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp

theorem emb_eq (h : Matrix (Fin n) (Fin n) ℂ) : emb e h = embL e h + emb e 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [emb, embL]

open scoped Matrix.Norms.Frobenius in
theorem deriv_conj (X : Matrix (Fin n) (Fin n) ℂ) (a b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    HasDerivAt (fun t : ℝ => a * emb e (NormedSpace.exp ((t : ℂ) • X)) * b) (a * embL e X * b) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at h1
  have h2 := (LinearMap.toContinuousLinearMap (embL e)).hasFDerivAt.comp_hasDerivAt 0 h1
  have h3 := ((h2.add_const (emb e 0)).const_mul a).mul_const b
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [emb_eq (e := e) (NormedSpace.exp ((t : ℂ) • X))]
  rfl

set_option maxHeartbeats 1600000 in
theorem lipschitz_estimate : Lip := by
  intro n ε lam ε' B e A _ _ _ π ν hν hF hn hl hDS hB hg v hv hv1 g₀ Y δ hY hδ hδ1 X hX
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  have hn1 : 1 ≤ n := by omega
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set b : ℕ := 2 * n ^ 2 + 1 with hb
  have hg' : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((n + 1 : ℕ) : ℝ) ^ 3) := by push_cast; exact hg
  have hY1 : 1 ≤ Y := (one_le_hsG (by omega) g₀).trans hY
  have hY0 : 0 ≤ hs (uMat g₀) := by rw [← nG_sq]; positivity
  have hNB : (n : ℝ) + 1 ≤ 4 * B := by have := le_four_mul (by omega) hl hB; push_cast at this; exact this
  have hB0 : 0 ≤ B := by linarith
  set T : ℝ := 8 * ((n : ℝ) + 1) * B * Y / δ with hT
  have T0 : 8 * ((n : ℝ) + 1) * B * Y ≤ T := by
    rw [hT, le_div_iff₀ hδ]
    exact mul_le_of_le_one_right (by have : 0 ≤ B := by linarith
                                     positivity) hδ1
  have T1 : 6 * (((n : ℝ) + 1) * Y) ≤ T := by
    have : 6 * (((n : ℝ) + 1) * Y) ≤ (8 * B) * (((n : ℝ) + 1) * Y) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have T2 : 18 ≤ T := by nlinarith
  have T3 : 16 * (n : ℝ) ^ 2 / δ ≤ T ^ 2 := by
    have : 16 * (n : ℝ) ^ 2 / δ ≤ 8 * T := by
      rw [hT, ← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hδ.le
      have : ((n : ℝ) + 1) * (n + 1) * 1 ≤ (n + 1) * (4 * B) * Y := by gcongr
      nlinarith
    nlinarith
  clear_value T
  have hsN : Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt n ≤ n + 1 := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_le_iff]
    push_cast
    exact ⟨by linarith, by nlinarith⟩
  have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by linarith)
  set P : ℝ := Real.exp 1 * Real.sqrt ((n + 1 : ℕ) : ℝ) * Y with hP
  set Q : ℝ := Real.sqrt n * Real.exp 2 with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hs1 (Real.one_le_exp (by norm_num))
  have T4 : P * Q ≤ T ^ 2 := by
    have e3 : Real.exp 1 * Real.exp 2 ≤ 27 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      have := Real.exp_one_lt_three
      have := Real.exp_pos 1
      nlinarith
    calc P * Q = (Real.exp 1 * Real.exp 2) * (Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt n) * Y := by rw [hP, hQ]; ring
      _ ≤ 27 * (n + 1) * Y := by gcongr
      _ ≤ T ^ 2 := by nlinarith
  set D : ℝ := (P * Q) ^ (2 * b) with hD
  have hD0 : 0 ≤ D := by positivity
  have hDT : D ≤ T ^ (4 * b) := by
    rw [show 4 * b = 2 * (2 * b) by ring, pow_mul T]
    exact pow_le_pow_left₀ (by positivity) T4 _

  let f : UJ ε' → ℂ := fun k => ⟪π (uMat g₀) v, π (uMat (embG hF k)) (π (uMat g₀) v)⟫_ℂ
  have hf : ∀ k, ‖f k‖ ≤ P ^ (2 * b) * (nG k)⁻¹ ^ (2 * b) := by
    intro k
    have h1 := dec_conj (by omega) hπ (by positivity)
      (dec_low (by omega) le_rfl hl hDS hg' hv hv1 (A := 2 * b) (by omega) (by simp only [hb]; nlinarith)) g₀ (embG hF k)
    refine h1.trans (mul_le_mul ?_ (pow_le_pow_left₀ (by unfold nG; positivity)
      (inv_anti₀ (by linarith [one_le_nG hn1 k]) (nG_le_embG hF k)) _) (by unfold nG; positivity) (by positivity))
    rw [hP, mul_pow _ Y]
    gcongr
  have hτ : ∀ k : UJ ε', 0 < (nG k)⁻¹ ^ b ∧ (nG k)⁻¹ ^ b ≤ 1 := fun k =>
    ⟨by have := one_le_nG hn1 k; positivity,
      pow_le_one₀ (by unfold nG; positivity) (inv_le_one_of_one_le₀ (one_le_nG hn1 k))⟩
  set r := Real.sqrt (hs X) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hfin : ∀ C : ℝ, 0 ≤ C → C ≤ 3 * T ^ (4 * b) * r →
      ENNReal.ofReal (C * (2 * (16 * (n : ℝ) ^ 2 / δ) ^ (2 * n ^ 2))) ≤ ENNReal.ofReal (T ^ (20 * (n + 1) ^ 2) * r) := by
    intro C hC hC'
    refine ENNReal.ofReal_le_ofReal ?_
    calc _ ≤ (3 * T ^ (4 * b) * r) * (2 * (T ^ 2) ^ (2 * n ^ 2)) := by gcongr
      _ = 6 * T ^ (4 * b + 4 * n ^ 2) * r := by
          rw [← pow_mul, pow_add T, show 2 * (2 * n ^ 2) = 4 * n ^ 2 by ring]; ring
      _ ≤ T * T ^ (4 * b + 4 * n ^ 2) * r := by gcongr; linarith
      _ = T ^ (4 * b + 4 * n ^ 2 + 1) * r := by rw [← pow_succ']
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by simp only [hb]; nlinarith)) hr0
  have hs0 : 0 ≤ hs X := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  set X' : Matrix (Fin n) (Fin n) ℂ := ((r⁻¹ : ℝ) : ℂ) • X with hX'd
  have hX' : inG ε' X' := by
    have : Xᴴ * Jm ε' + Jm ε' * X = 0 := hX
    unfold inG
    rw [hX'd, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul,
      ← smul_add, this, smul_zero]
  have hX1 : hs X' ≤ 1 := by
    rw [hX'd, hs_smul, inv_pow, hr, Real.sq_sqrt hs0]
    exact inv_mul_le_one_of_le₀ le_rfl hs0
  have hXr : ((-r : ℝ) : ℂ) • X' = -X := by
    rcases hr0.eq_or_lt with h | h
    · have : X = 0 := eq_zero_of_hs (by rw [← Real.sq_sqrt hs0, ← hr, ← h]; ring)
      simp [hX'd, this]
    · rw [hX'd, smul_smul, ← Complex.ofReal_mul, neg_mul, mul_inv_cancel₀ h.ne']; simp
  obtain ⟨c, hc, hc0, hadd⟩ := exists_onePar hX'
  have hinv : ∀ s, (c s)⁻¹ = c (-s) := fun s => by
    rw [inv_eq_iff_mul_eq_one, ← hadd, add_neg_cancel, hc0]
  have hgoal : ∀ h : UJ ε', emb e (NormedSpace.exp (-X) * um h) = uMat (embG hF ((c r)⁻¹ * h)) := by
    intro h
    rw [hinv, ← hXr, ← hc]
    rfl
  simp only [hgoal]
  change ∫⁻ h, ‖f ((c r)⁻¹ * h) - f h‖ₑ ∂ν ≤ _ * ν (nearSet ε' δ)
  have hPD : P ^ (2 * b) ≤ D := pow_le_pow_left₀ hP0 (le_mul_of_one_le_right hP0 hQ1) _
  rcases le_total 1 r with hr1 | hr1
  · let F : UJ ε' → ℂ := fun k => ((D * (nG k)⁻¹ ^ b : ℝ) : ℂ)
    have hFn : ∀ k, ‖F k‖ = D * (nG k)⁻¹ ^ b := fun k => by
      rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hD0 (hτ k).1.le)]
    have hfF : ∀ k, ‖f k‖ₑ ≤ ‖F k‖ₑ := fun k => by
      rw [enorm_le_iff_norm_le, hFn]
      refine (hf k).trans (mul_le_mul hPD ?_ (by unfold nG; positivity) hD0)
      rw [two_mul, pow_add]
      exact mul_le_of_le_one_right (hτ k).1.le (hτ k).2
    have hFm : Measurable fun k => ‖F k‖ₑ := by
      have : Continuous (nG (ε := ε')) := (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε')).sqrt
      exact (Complex.measurable_ofReal.comp (measurable_const.mul (this.measurable.inv.pow_const b))).enorm
    have h1 := lint_le hn1 ν hD0 hδ hδ1 (f := F) fun k => (hFn k).le
    calc _ ≤ ∫⁻ h, ‖F ((c r)⁻¹ * h)‖ₑ + ‖F h‖ₑ ∂ν :=
          lintegral_mono fun h => enorm_sub_le.trans (add_le_add (hfF _) (hfF _))
      _ = 2 * ∫⁻ h, ‖F h‖ₑ ∂ν := by
          rw [lintegral_add_right _ hFm, lintegral_mul_left_eq_self (fun h => ‖F h‖ₑ), two_mul]
      _ ≤ 2 * (ENNReal.ofReal (D * (2 * (16 * (n : ℝ) ^ 2 / δ) ^ (2 * n ^ 2))) * ν (nearSet ε' δ)) :=
          mul_le_mul_right h1 _
      _ = ENNReal.ofReal ((2 * D) * (2 * (16 * (n : ℝ) ^ 2 / δ) ^ (2 * n ^ 2))) * ν (nearSet ε' δ) := by
          rw [← mul_assoc, mul_assoc 2 D, ENNReal.ofReal_mul zero_le_two]; simp
      _ ≤ _ := by
          refine mul_le_mul_left (hfin _ (by positivity) ?_) _
          have : 0 ≤ T ^ (4 * b) := by positivity
          nlinarith
  · obtain ⟨x, hx, -, hb2⟩ := low_bounds (by omega) hl hDS hB
      (fun a a' h => le_trans (by push_cast; have : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
                                  linarith) (hg a a' h)) hv hv1
    let d : ℝ → UJ ε := fun s => g₀⁻¹ * embG hF (c s) * g₀
    have d0 : d 0 = 1 := by simp [d, hc0]
    have dadd : ∀ s t, d (s + t) = d s * d t := fun s t => by simp only [d, hadd, map_mul]; group
    have dd : HasDerivAt (fun t => uMat (d t)) (uMat g₀⁻¹ * embL e X' * uMat g₀) 0 := by
      have e0 : (fun t => uMat (d t)) = fun t : ℝ => uMat g₀⁻¹ * emb e (NormedSpace.exp ((t : ℂ) • X')) * uMat g₀ := by
        funext t
        rw [← hc]
        rfl
      rw [e0]
      exact deriv_conj X' _ _
    set Z := uMat g₀⁻¹ * embL e X' * uMat g₀ with hZ
    have hZ1 : Real.sqrt (hs Z) ≤ Y := by
      have a1 : Real.sqrt (hs (embL e X')) ≤ 1 := by
        refine Real.sqrt_le_one.2 ?_
        change hs (Matrix.reindex e e (Matrix.fromBlocks X' 0 0 0)) ≤ 1
        rw [hs_block]; simpa using hX1
      have a2 : Real.sqrt (hs (uMat g₀⁻¹)) = nG g₀ := nG_inv g₀
      have a3 : 0 ≤ nG g₀ := Real.sqrt_nonneg _
      calc _ ≤ Real.sqrt (hs (uMat g₀⁻¹ * embL e X')) * nG g₀ := sqrt_frobenius_mul_le _ _
        _ ≤ (nG g₀ * 1) * nG g₀ := by
            refine mul_le_mul_of_nonneg_right ((sqrt_frobenius_mul_le _ _).trans ?_) a3
            rw [a2]; gcongr
        _ = hs (uMat g₀) := by rw [← nG_sq]; ring
        _ ≤ Y := hY
    clear_value Z
    have hM : ‖actM (smE ε π) Z (actM (smE ε π) Z x)‖ ≤ T ^ (4 * b) := by
      refine (hb2 Z).trans ?_
      have hZ0 : 0 ≤ hs Z := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
      have a1 : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ n + 1 :=
        (le_mul_of_one_le_right (Real.sqrt_nonneg _) hs1).trans hsN
      have a2 : Real.sqrt (hs Z) * (8 * Real.sqrt ((n + 1 : ℕ) : ℝ) * (B + 2)) ≤ T ^ 2 := by
        calc _ ≤ Y * (8 * (n + 1) * (4 * B)) := by gcongr <;> linarith
          _ = 4 * (8 * ((n : ℝ) + 1) * B * Y) := by ring
          _ ≤ 4 * T := by linarith
          _ ≤ T ^ 2 := by nlinarith
      calc _ = (Real.sqrt (hs Z) * (8 * Real.sqrt ((n + 1 : ℕ) : ℝ) * (B + 2))) ^ 2 := by
            rw [mul_pow (Real.sqrt (hs Z)), Real.sq_sqrt hZ0]
        _ ≤ (T ^ 2) ^ 2 := pow_le_pow_left₀ (by have : 0 ≤ B := by linarith
                                                positivity) a2 2
        _ = T ^ 4 := by ring
        _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
    refine (lint_le hn1 ν (C := 3 * T ^ (4 * b) * r) (by positivity) hδ hδ1 fun h => ?_).trans
      (mul_le_mul_left (hfin _ (by positivity) le_rfl) _)
    set u : A := π (uMat (g₀⁻¹ * embG hF h * g₀)) v with hu
    have hid : ∀ s, ⟪π (uMat (d s)) (x : A), u⟫_ℂ = f ((c s)⁻¹ * h) := by
      intro s
      have a1 := hπ.1.2 _ (embG hF ((c s)⁻¹ * h)).2 _ g₀.2
      have a2 : π (uMat (embG hF ((c s)⁻¹ * h))) (π (uMat g₀) v) = π (uMat (embG hF ((c s)⁻¹ * h) * g₀)) v := by
        change _ = π (uMat (embG hF ((c s)⁻¹ * h)) * uMat g₀) v
        rw [a1]; rfl
      simp only [f]
      rw [hx, hu, a2, inner_move hπ, inner_move hπ]
      congr 3
      simp only [d, map_mul, map_inv]
      group
    have hη : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖⟪π (uMat (d s)) (x : A), u⟫_ℂ‖ ≤ D * ((nG h)⁻¹ ^ b) ^ 2 := by
      intro s hs'
      rw [hid]
      refine (hf _).trans ?_
      have a1 : nG (c s) ≤ Q := by
        unfold nG
        rw [hc, Real.sqrt_le_iff]
        refine ⟨by positivity, (ReciprocityTheory.ChartRestriction.DS.S7.hs_exp_leVG _).trans ?_⟩
        have a2 : Real.sqrt (ReciprocityTheory.ChartRestriction.DS.S7.hs ((s : ℂ) • X')) ≤ 2 := by
          change Real.sqrt (hs _) ≤ 2
          rw [hs_smul, Real.sqrt_le_iff]
          refine ⟨by norm_num, ?_⟩
          have : 0 ≤ hs X' := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
          have : s ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ hs'.1 hs'.2 2
          nlinarith
        rw [hQ, mul_pow, Real.sq_sqrt (by linarith), ← Real.exp_nat_mul]
        gcongr
        push_cast
        linarith
      have a3 : nG h ≤ Q * nG ((c s)⁻¹ * h) := by
        have := nG_mul (c s) ((c s)⁻¹ * h)
        rw [mul_inv_cancel_left] at this
        exact this.trans (mul_le_mul_of_nonneg_right a1 (Real.sqrt_nonneg _))
      have a4 := one_le_nG hn1 h
      have a5 := one_le_nG hn1 ((c s)⁻¹ * h)
      have a6 : (nG ((c s)⁻¹ * h))⁻¹ ≤ Q * (nG h)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_le_iff₀ (by linarith)]; linarith
      calc _ ≤ P ^ (2 * b) * (Q * (nG h)⁻¹) ^ (2 * b) := by gcongr
        _ = _ := by rw [hD]; ring
    have h1 := coef_interp hπ x d0 dadd dd (by rw [hu, hπ.2.1 _ (g₀⁻¹ * embG hF h * g₀).2, hv1]) hM hη (hτ h).1 (hτ h).2
      ⟨hr0, hr1⟩
    rw [hid, hid, hc0, inv_one, one_mul] at h1
    refine h1.trans ?_
    have a1 := (hτ h).1
    have e1 : 2 * (D * ((nG h)⁻¹ ^ b) ^ 2) / (nG h)⁻¹ ^ b = 2 * D * (nG h)⁻¹ ^ b := by field_simp
    rw [e1]
    have : 0 ≤ (nG h)⁻¹ ^ b * r := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hDT this]

theorem analytic_estimates : Analysis := ⟨volume_ratio_bound, decay_estimate, integral_ratio_bound, h_integrability, derivative_upper_bound, lipschitz_estimate⟩

end CompanionTheory.Lime.T3
