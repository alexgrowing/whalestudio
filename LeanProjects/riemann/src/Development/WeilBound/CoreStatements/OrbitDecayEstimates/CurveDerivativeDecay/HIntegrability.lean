import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.OrbitDeriv
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HeBranching

noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

variable {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}

theorem emb_mul (a b : Matrix (Fin n) (Fin n) ℂ) : emb e (a * b) = emb e a * emb e b := by
  simp [emb, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem emb_one : emb e (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp [emb, Matrix.fromBlocks_one]

theorem emb_conjT (a : Matrix (Fin n) (Fin n) ℂ) : (emb e a)ᴴ = emb e aᴴ := by
  simp [emb, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

theorem emb_J (hF : Fits ε ε' e) : emb e (Jm ε') = Jm ε := by
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  have h1 : ε (e (Sum.inr ())) = true := hF.1
  rcases i with i | i <;> rcases j with j | j <;> simp [emb, Jm, Matrix.diagonal_apply, hF.2, h1]

theorem hs_block (a : Matrix (Fin n) (Fin n) ℂ) (d : Matrix Unit Unit ℂ) :
    hs (Matrix.reindex e e (Matrix.fromBlocks a 0 0 d)) = hs a + ‖d () ()‖ ^ 2 := by
  unfold hs
  rw [← e.sum_comp]
  simp_rw [← e.sum_comp (fun j => ‖Matrix.reindex e e (Matrix.fromBlocks a 0 0 d) _ j‖ ^ 2)]
  simp [Fintype.sum_sum_type]

theorem col_emb (g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : Matrix (Fin n) (Fin n) ℂ) :
    colSq (g * emb e a) (zi e) = colSq g (zi e) := by
  unfold colSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, ← e.sum_comp]
  simp [emb, zi, Fintype.sum_sum_type]

def embG (hF : Fits ε ε' e) : UJ ε' →* UJ ε where
  toFun h := ⟨⟨emb e (uMat h), emb e (uMat h⁻¹), by rw [← emb_mul, ← emb_one (e := e)]; congr 1; exact determinant_character_mul_inv h,
      by rw [← emb_mul, ← emb_one (e := e)]; congr 1; exact (show (h : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹.1 * _ = 1 from Units.inv_mul _)⟩, by
    have hh : (uMat h)ᴴ * Jm ε' * uMat h = Jm ε' := h.2
    show (emb e (uMat h))ᴴ * Jm ε * emb e (uMat h) = Jm ε
    rw [← emb_J hF, emb_conjT, ← emb_mul, ← emb_mul, hh]⟩
  map_one' := Subtype.ext (Units.ext emb_one)
  map_mul' a b := Subtype.ext (Units.ext (emb_mul _ _))

theorem uMat_embG (hF : Fits ε ε' e) (h : UJ ε') : uMat (embG hF h) = emb e (uMat h) := rfl

theorem nG_le_embG (hF : Fits ε ε' e) (h : UJ ε') : nG h ≤ nG (embG hF h) := by
  unfold nG
  rw [uMat_embG, emb, hs_block]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity))

theorem colSq_le_hs {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) : colSq g j ≤ hs g :=
  Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun k => ‖g i k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)

theorem colSq_pos {m : ℕ} {η : Fin m → Bool} (g : UJ η) (j : Fin m) : 0 < colSq (uMat g) j := by
  by_contra h
  have h0 : colSq (uMat g) j = 0 := le_antisymm (not_lt.1 h) (Finset.sum_nonneg fun _ _ => by positivity)
  have h1 : ∀ i, uMat g i j = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).1 h0 i (Finset.mem_univ i)
    simpa using this
  have h2 : uMat g⁻¹ * uMat g = 1 := Units.inv_mul (g : (Matrix (Fin m) (Fin m) ℂ)ˣ)
  have h3 := congrFun (congrFun h2 j) j
  simp [Matrix.mul_apply, h1] at h3

theorem rpow_hs {m : ℕ} (hm : 1 ≤ m) {η : Fin m → Bool} (g : UJ η) (k : ℕ) {a : ℝ} (ha : (k : ℝ) ≤ 2 * a) :
    hs (uMat g) ^ (-a) ≤ (nG g)⁻¹ ^ k := by
  have h1 := one_le_nG hm g
  rw [← nG_sq, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), inv_pow, ← Real.rpow_natCast,
    ← Real.rpow_neg (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le h1 (by push_cast; linarith)

theorem lint_le {m : ℕ} (hm : 1 ≤ m) {η : Fin m → Bool} (μ : Measure (UJ η)) [μ.IsHaarMeasure] {f : UJ η → ℂ} {C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : ∀ g, ‖f g‖ ≤ C * (nG g)⁻¹ ^ (2 * m ^ 2 + 1)) :
    ∫⁻ g, ‖f g‖ₑ ∂μ ≤ ENNReal.ofReal (C * (2 * (16 * (m : ℝ) ^ 2 / δ) ^ (2 * m ^ 2))) * μ (nearSet η δ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsq : Real.sqrt m ≤ m := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  calc ∫⁻ g, ‖f g‖ₑ ∂μ ≤ ∫⁻ g, ENNReal.ofReal C * ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ (2 * m ^ 2 + 1)) ∂μ := by
        refine lintegral_mono fun g => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hd g)
    _ = ENNReal.ofReal C * ∫⁻ g, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ (2 * m ^ 2 + 1)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 * (16 * (m : ℝ) ^ 2 / δ) ^ (2 * m ^ 2)) * μ (nearSet η δ)) := by
        refine mul_le_mul_right ((int_ratio hm η μ hδ (by linarith) le_rfl).trans (mul_le_mul_left ?_ _)) _
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) zero_le_two)
        exact div_le_div_of_nonneg_right (by nlinarith) hδ.le
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hC]

theorem h_integrability : HInt := by
  intro n ε ε' e ν hν hF hn φ C δ hC hδ hδ1 hd g
  set b : ℕ := 2 * n ^ 2 + 1 with hb
  set a : ℕ := 2 * (n + 1) + 5 with ha
  have hn1 : 1 ≤ n + 1 := by omega
  have hbd : BddBelow (Set.range fun h => nG (g * embG hF h)) := ⟨1, by rintro _ ⟨h, rfl⟩; exact one_le_nG hn1 _⟩
  have hi1 : 1 ≤ ⨅ h, nG (g * embG hF h) := le_ciInf fun h => one_le_nG hn1 _
  obtain ⟨h1, hh1⟩ := exists_lt_of_ciInf_lt (show (⨅ h, nG (g * embG hF h)) < 2 * ⨅ h, nG (g * embG hF h) by linarith)
  set g1 := g * embG hF h1 with hg1
  set y := colSq (uMat g) (zi e) with hy
  have hy0 : 0 < y := colSq_pos g _
  have hG1 := one_le_nG hn1 g1
  have hyG : Real.sqrt y ≤ nG g1 := by
    refine Real.sqrt_le_sqrt ?_
    rw [hy, ← col_emb (e := e) (uMat g) (uMat h1)]
    exact colSq_le_hs _ _
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hpt : ∀ h : UJ ε', ‖φ (um g * emb e (um (h1 * h)))‖ ≤
      (C * 2 ^ (a + b) * (Real.sqrt y)⁻¹ ^ a) * (nG h)⁻¹ ^ b := by
    intro h
    have e1 : um g * emb e (um (h1 * h)) = uMat (g1 * embG hF h) := by
      rw [hg1, mul_assoc, ← map_mul]; rfl
    set t := nG (g1 * embG hF h) with ht
    have ht1 : 1 ≤ t := one_le_nG hn1 _
    have hh := one_le_nG (by omega : 1 ≤ n) h
    have t1 : nG g1 ≤ 2 * t := by
      have := ciInf_le hbd (h1 * h)
      rw [map_mul, ← mul_assoc] at this
      linarith
    have t2 : nG h ≤ nG g1 * t := by
      refine (nG_le_embG hF h).trans ?_
      have := nG_mul g1⁻¹ (g1 * embG hF h)
      rwa [inv_mul_cancel_left, nG_inv] at this
    have s1 : t⁻¹ ≤ 2 * (nG g1)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_le_iff₀ (by linarith)]; linarith
    have s2 : t⁻¹ ≤ nG g1 * (nG h)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_le_iff₀ (by linarith)]; linarith
    have s3 := rpow_hs hn1 (g1 * embG hF h) (a + b + b) (a := 3 * ((n : ℝ) + 1) ^ 2) (by
      simp only [ha, hb]; push_cast; have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith)
    have s4 : t⁻¹ ^ (a + b + b) ≤ (2 * (nG g1)⁻¹) ^ (a + b) * (nG g1 * (nG h)⁻¹) ^ b := by
      rw [pow_add _ (a + b)]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) s1 _) (pow_le_pow_left₀ (by positivity) s2 _) (by positivity)
        (by positivity)
    have s5 : (2 * (nG g1)⁻¹) ^ (a + b) * (nG g1 * (nG h)⁻¹) ^ b = 2 ^ (a + b) * (nG g1)⁻¹ ^ a * (nG h)⁻¹ ^ b := by
      have : (nG g1)⁻¹ ^ b * nG g1 ^ b = 1 := by rw [← mul_pow, inv_mul_cancel₀ (by linarith), one_pow]
      rw [mul_pow, mul_pow, pow_add (nG g1)⁻¹]
      linear_combination (2 ^ (a + b) * (nG g1)⁻¹ ^ a * (nG h)⁻¹ ^ b) * this
    have s6 : (nG g1)⁻¹ ^ a ≤ (Real.sqrt y)⁻¹ ^ a := pow_le_pow_left₀ (by positivity) (inv_anti₀ hsy hyG) a
    rw [e1]
    refine (hd _).trans ?_
    calc C * hs (uMat (g1 * embG hF h)) ^ (-(3 * ((n : ℝ) + 1) ^ 2))
        ≤ C * (2 ^ (a + b) * (Real.sqrt y)⁻¹ ^ a * (nG h)⁻¹ ^ b) := by
          refine mul_le_mul_of_nonneg_left (s3.trans (s4.trans (s5.le.trans ?_))) hC
          gcongr
      _ = _ := by ring
  rw [← lintegral_mul_left_eq_self (fun h : UJ ε' => ‖φ (um g * emb e (um h))‖ₑ) h1]
  refine (lint_le (by omega) ν (by positivity) hδ hδ1 hpt).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  have e2 : (Real.sqrt y)⁻¹ ^ a = y ^ (-((2 * ((n : ℝ) + 1) + 5) / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy0.le, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    congr 1
    simp only [ha]; push_cast; ring
  set T : ℝ := 100 * ((n : ℝ) + 1) ^ 2 / δ with hT
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have T1 : 16 * (n : ℝ) ^ 2 / δ ≤ T := div_le_div_of_nonneg_right (by nlinarith) hδ.le
  have T2 : 2 ≤ T := by rw [hT, le_div_iff₀ hδ]; nlinarith
  have T3 : (2 : ℝ) ^ (a + b) * (2 * (16 * (n : ℝ) ^ 2 / δ) ^ (2 * n ^ 2)) ≤ T ^ (10 * (n + 1) ^ 2) := by
    calc _ ≤ T ^ (a + b) * (T * T ^ (2 * n ^ 2)) := by gcongr
      _ = T ^ (a + b + 1 + 2 * n ^ 2) := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by simp only [ha, hb]; nlinarith)
  rw [e2]
  calc _ = C * (2 ^ (a + b) * (2 * (16 * (n : ℝ) ^ 2 / δ) ^ (2 * n ^ 2))) * y ^ (-((2 * ((n : ℝ) + 1) + 5) / 2)) := by ring
    _ ≤ _ := by gcongr

end CompanionTheory.Lime.T3
