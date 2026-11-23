import Formalism.HermitianCurvature.StatementG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionCriticalPoints
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AffineChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs

open Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.OrbitTailEstimates

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7

theorem min_le_maxpow (A y : ℝ) : min 1 (y ^ (-A)) ≤ (max 1 y) ^ (-A) := by
  rcases le_total y 1 with h | h
  · rw [max_eq_left h, Real.one_rpow]; exact min_le_left _ _
  · rw [max_eq_right h]; exact min_le_right _ _

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem integrable_maxpow (ν : Measure E) [ν.IsAddHaarMeasure] (B : ℝ)
    (hB : (Module.finrank ℝ E : ℝ) < B) : Integrable (fun q : E => (max 1 ‖q‖) ^ (-B)) ν := by
  have h0 : Integrable (fun q : E => (1 + ‖q‖) ^ (-B)) ν := integrable_one_add_norm hB
  have hB0 : 0 ≤ B := le_trans (Nat.cast_nonneg _) hB.le
  refine Integrable.mono' (h0.const_mul (2 ^ B)) ?_ (Filter.Eventually.of_forall fun q => ?_)
  · exact (Continuous.rpow_const (by fun_prop) (fun q => Or.inl (by positivity))).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have h1 : (0 : ℝ) < 1 + ‖q‖ := by positivity
    have e : (2 : ℝ) ^ B * (1 + ‖q‖) ^ (-B) = ((1 + ‖q‖) / 2) ^ (-B) := by
      rw [Real.div_rpow h1.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) B]
      field_simp
    rw [e]
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    have := le_max_left 1 ‖q‖
    have := le_max_right 1 ‖q‖
    linarith

theorem maxpow_scale (T A : ℝ) (hT : 0 < T) (q : E) :
    (max T ‖q‖) ^ (-A) = T ^ (-A) * (max 1 ‖T⁻¹ • q‖) ^ (-A) := by
  have e : max T ‖q‖ = T * max 1 ‖T⁻¹ • q‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hT.le), mul_max_of_nonneg _ _ hT.le, mul_one,
      mul_inv_cancel_left₀ hT.ne']
  rw [e, Real.mul_rpow hT.le (by positivity)]

theorem tail_haar (ν : Measure E) [ν.IsAddHaarMeasure] (T A : ℝ) (hT : 1 ≤ T)
    (hA : (Module.finrank ℝ E : ℝ) + 1 ≤ A) :
    Integrable (fun q : E => (max T ‖q‖) ^ (-A)) ν ∧
    ∫ q : E, (max T ‖q‖) ^ (-A) ∂ν ≤
      T ^ ((Module.finrank ℝ E : ℝ) - A) * ∫ q : E, (max 1 ‖q‖) ^ (-((Module.finrank ℝ E : ℝ) + 1)) ∂ν := by
  have hT0 : 0 < T := by linarith
  have hIA : Integrable (fun q : E => (max 1 ‖q‖) ^ (-A)) ν := integrable_maxpow ν A (by linarith)
  have hIB : Integrable (fun q : E => (max 1 ‖q‖) ^ (-((Module.finrank ℝ E : ℝ) + 1))) ν :=
    integrable_maxpow ν _ (by linarith)
  have hfun : (fun q : E => (max T ‖q‖) ^ (-A)) = fun q : E => T ^ (-A) * (max 1 ‖T⁻¹ • q‖) ^ (-A) :=
    funext fun q => maxpow_scale T A hT0 q
  constructor
  · rw [hfun]
    exact (hIA.comp_smul (inv_ne_zero hT0.ne')).const_mul _
  · rw [hfun, integral_const_mul, Measure.integral_comp_inv_smul ν (fun q : E => (max 1 ‖q‖) ^ (-A)) T,
      abs_of_nonneg (by positivity), smul_eq_mul, ← mul_assoc]
    have e : T ^ ((Module.finrank ℝ E : ℝ) - A) = T ^ (-A) * T ^ (Module.finrank ℝ E) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hT0]; congr 1; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine integral_mono hIA hIB fun q => ?_
    exact Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith)

theorem tail_smul (ν μ : Measure E) [ν.IsAddHaarMeasure] (k : NNReal) (hμ : μ = k • ν) (T A : ℝ) (hT : 1 ≤ T)
    (hA : (Module.finrank ℝ E : ℝ) + 1 ≤ A) :
    Integrable (fun q : E => (max T ‖q‖) ^ (-A)) μ ∧
    ∫ q : E, (max T ‖q‖) ^ (-A) ∂μ ≤
      T ^ ((Module.finrank ℝ E : ℝ) - A) * ∫ q : E, (max 1 ‖q‖) ^ (-((Module.finrank ℝ E : ℝ) + 1)) ∂μ := by
  obtain ⟨h1, h2⟩ := tail_haar ν T A hT hA
  subst hμ
  refine ⟨h1.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def, smul_eq_mul,
    smul_eq_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left h2 k.coe_nonneg

end General

theorem norm_coordMap_le (n : ℕ) (t c : ℂ) (p : BlockCoord n) : ‖coordMap n t p‖ ≤ ‖orbM n t c p‖ := by
  refine norm_coord_le t (c + p.1 ⬝ᵥ (wMat n *ᵥ (t • p.2.2))) (t • p.2.1) (t • p.2.2)
    (rhoOf t p.1 p.2.1) (orbM n t c p) ?_
  rw [strictUpper_smul]
  exact matrix_entries n t c p

theorem norm_orbM_ge (m : ℕ) (t c : ℂ) (p : BlockCoord (m + 1)) : ‖t‖ ≤ ‖orbM (m + 1) t c p‖ := by
  have hX : IsStrictUpper (Xof t p.2.1) := by
    unfold Xof
    rw [← strictUpper_smul]
    exact isStrictUpper_strictUpper _
  have h := (shape_of_matrix m t (c + p.1 ⬝ᵥ (wMat (m + 1) *ᵥ (t • p.2.2))) (Xof t p.2.1) (t • p.2.2)
    (rhoOf t p.1 p.2.1) hX).2.1 0 ⟨m, by omega⟩ (by simp)
  have e0 : orbM (m + 1) t c p = Mcoord t (Xof t p.2.1) (t • p.2.2) (rhoOf t p.1 p.2.1)
      (c + p.1 ⬝ᵥ (wMat (m + 1) *ᵥ (t • p.2.2))) := matrix_entries (m + 1) t c p
  have e : orbM (m + 1) t c p 0 ⟨m, by omega⟩ = t := by
    rw [e0]; exact h
  calc ‖t‖ = ‖orbM (m + 1) t c p 0 ⟨m, by omega⟩‖ := by rw [e]
    _ ≤ _ := norm_entry_le _ _ _

theorem detM_orbM (n : ℕ) (t c : ℂ) (p : BlockCoord n) :
    detM (orbM n t c p) = (wMat n).det * (c * t ^ n) := det_orbit.1 n t c p

theorem norm_blockIntegrand {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (n : ℕ)
    (Φ : Mat (n + 1) → V) (t c : ℂ) (p : BlockCoord n) :
    ‖blockIntegrand β n Φ t c p‖ = ‖Φ (orbM n t c p)‖ := by
  unfold blockIntegrand orbM
  rw [norm_smul, norm_mul, (additive_character_psi β _ 0).2.1, (additive_character_psi β _ 0).2.1, one_mul, one_mul]

theorem finrank_block_cast (m : ℕ) :
    (Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) = ((m : ℝ) + 1) * ((m : ℝ) + 4) := by
  rw [finrank_block]; push_cast; ring

theorem K_nonneg {x y K A : ℝ} (hy : 0 < y) (hx : 0 ≤ x) (h : x ≤ K * min 1 (y ^ (-A))) : 0 ≤ K := by
  have hpos : 0 < min 1 (y ^ (-A)) := lt_min one_pos (Real.rpow_pos_of_pos hy _)
  by_contra hK
  have : K * min 1 (y ^ (-A)) < 0 := mul_neg_of_neg_of_pos (not_le.1 hK) hpos
  linarith

theorem tailBound : TailBound := by
  intro m β
  refine ⟨∫ q : BlockCoord (m + 1), (max 1 ‖q‖) ^ (-((Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) + 1))
    ∂(muBlock β (m + 1)), ?_⟩
  intro V _ _ _ Φ A K τ t c hA hτ ht hΦ hvan
  have ht0 : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hA0 : 0 ≤ A := by
    have : (0 : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 4) := by positivity
    linarith
  have hb : ∀ p : BlockCoord (m + 1),
      ‖Φ (orbM (m + 1) t c p)‖ ≤ K * min 1 (‖orbM (m + 1) t c p‖ ^ (-A)) := by
    intro p
    have h3 := (hΦ (orbM (m + 1) t c p) (by rw [detM_orbM]; exact Set.mem_singleton _)).2 0 le_rfl
    rwa [norm_iteratedFDeriv_zero] at h3
  have hK : 0 ≤ K := K_nonneg (ht0.trans_le (norm_orbM_ge m t c 0)) (norm_nonneg _) (hb 0)
  set T : ℝ := max 1 τ with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  have hpt : ∀ p : BlockCoord (m + 1),
      ‖blockIntegrand β (m + 1) Φ t c p‖ ≤ K * (max T ‖coordMap (m + 1) t p‖) ^ (-A) := by
    intro p
    rw [norm_blockIntegrand]
    rcases lt_or_ge ‖orbM (m + 1) t c p‖ τ with h | h
    · rw [hvan p h, norm_zero]; positivity
    · refine (hb p).trans (mul_le_mul_of_nonneg_left ((min_le_maxpow A _).trans ?_) hK)
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
      refine max_le (max_le (le_max_left _ _) (h.trans (le_max_right _ _))) ?_
      exact (norm_coordMap_le (m + 1) t c p).trans (le_max_right _ _)
  obtain ⟨k, hk⟩ := muBlock_eq β (m + 1)
  have i1 : SecondCountableTopology ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ)) := inferInstance
  have i2 : BorelSpace ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ)) := inferInstance
  have i3 : BorelSpace (BlockCoord (m + 1)) := inferInstance
  have j1 : (volume : Measure ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have j2 : (volume : Measure (BlockCoord (m + 1))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨hI, hle⟩ := tail_smul volume (muBlock β (m + 1)) k hk T A hT1 (by rw [finrank_block_cast]; exact hA)
  have hJ := jacobian (m + 1) β t ht
  have hI' : Integrable (fun p : BlockCoord (m + 1) => (max T ‖coordMap (m + 1) t p‖) ^ (-A))
      (muBlock β (m + 1)) := by
    have h2 : Integrable (fun q : BlockCoord (m + 1) => (max T ‖q‖) ^ (-A))
        (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) := hJ ▸ hI.smul_measure_nnreal
    exact (embedding_coordMap _ t ht).integrable_map_iff.1 h2
  have hint : ∫ p : BlockCoord (m + 1), (max T ‖coordMap (m + 1) t p‖) ^ (-A) ∂(muBlock β (m + 1)) =
      (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * ∫ q : BlockCoord (m + 1), (max T ‖q‖) ^ (-A) ∂(muBlock β (m + 1)) := by
    rw [← (embedding_coordMap _ t ht).integral_map (fun q : BlockCoord (m + 1) => (max T ‖q‖) ^ (-A)), hJ,
      integral_smul_nnreal_measure, NNReal.smul_def, Real.coe_toNNReal _ (by positivity), smul_eq_mul]
  calc ‖OmBlock β (m + 1) Φ t c‖
      ≤ ∫ p : BlockCoord (m + 1), K * (max T ‖coordMap (m + 1) t p‖) ^ (-A) ∂(muBlock β (m + 1)) :=
        norm_integral_le_of_norm_le (hI'.const_mul K) (Filter.Eventually.of_forall hpt)
    _ = K * ((‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ *
          ∫ q : BlockCoord (m + 1), (max T ‖q‖) ^ (-A) ∂(muBlock β (m + 1))) := by
        rw [integral_const_mul, hint]
    _ ≤ K * ((‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * (T ^ ((Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) - A) *
          ∫ q : BlockCoord (m + 1), (max 1 ‖q‖) ^ (-((Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) + 1))
            ∂(muBlock β (m + 1)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by positivity)) hK
    _ = _ := by rw [finrank_block_cast]; ring

theorem pow_arith (m : ℕ) (x : ℝ) (hx : 0 < x) :
    x ^ ((m + 1) ^ 2) * ((x ^ ((m + 1) * (m + 4)))⁻¹ * x ^ (3 * m + 4)) = x := by
  have e : x ^ ((m + 1) ^ 2) * x ^ (3 * m + 4) = x ^ ((m + 1) * (m + 4)) * x := by
    rw [← pow_add, ← pow_succ]; congr 1; ring
  have h0 : x ^ ((m + 1) * (m + 4)) ≠ 0 := (pow_pos hx _).ne'
  calc x ^ ((m + 1) ^ 2) * ((x ^ ((m + 1) * (m + 4)))⁻¹ * x ^ (3 * m + 4))
      = (x ^ ((m + 1) * (m + 4)))⁻¹ * (x ^ ((m + 1) ^ 2) * x ^ (3 * m + 4)) := by ring
    _ = x := by rw [e, inv_mul_cancel_left₀ h0]

theorem tailStepOfBound : TailStepOfBound := by
  intro hTB hCut hCP m β
  obtain ⟨C1, hC1⟩ := hTB m β
  obtain ⟨C2, hC2⟩ := hCP (m + 1 + 1) 0
  refine ⟨C1 * C2, ?_⟩
  intro V _ _ _ Φ A K ε t c hε hε1 hA ht ht1 hΦ
  have ht0 : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set τ : ℝ := ‖t‖ ^ (-ε) with hτ
  have hτ1 : 1 ≤ τ := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
  have hτ0 : 0 < τ := by linarith
  have hD := (hC2 V Φ _ _ τ hτ1 hΦ).2
  have hD' : DerivBound 0 {(wMat (m + 1)).det * (c * t ^ (m + 1))}
      (fun Z => (C2 * K) * min 1 (‖Z‖ ^ (-A))) (cutPhiC τ Φ) := by
    intro Z hZ
    obtain ⟨h1, h2⟩ := hD Z hZ
    refine ⟨h1, fun j hj => ?_⟩
    have h3 : ‖iteratedFDeriv ℝ j (cutPhiC τ Φ) Z‖ ≤ C2 * (K * min 1 (‖Z‖ ^ (-A))) := h2 j hj
    show ‖iteratedFDeriv ℝ j (cutPhiC τ Φ) Z‖ ≤ C2 * K * min 1 (‖Z‖ ^ (-A))
    rwa [mul_assoc]
  have hvan : ∀ p : BlockCoord (m + 1), ‖orbM (m + 1) t c p‖ < τ →
      cutPhiC τ Φ (orbM (m + 1) t c p) = 0 := by
    intro p hp
    unfold cutPhiC
    rw [((hCut (m + 1 + 1)).1 τ _ hτ0).2.2.1 hp.le]
    simp
  have hq : 3 * (m : ℝ) + 4 ≤ (A - ((m : ℝ) + 1) * ((m : ℝ) + 4)) * ε := by
    rw [← div_le_iff₀ hε]; linarith
  have hN : ((m : ℝ) + 1) * ((m : ℝ) + 4) + 1 ≤ A := by
    have h1 : (A - ((m : ℝ) + 1) * ((m : ℝ) + 4)) * ε ≤ A - ((m : ℝ) + 1) * ((m : ℝ) + 4) := by
      have h2 : 0 ≤ A - ((m : ℝ) + 1) * ((m : ℝ) + 4) := by
        have : 0 ≤ (3 * (m : ℝ) + 4) / ε := by positivity
        linarith
      nlinarith
    linarith
  have h := hC1 V (cutPhiC τ Φ) A (C2 * K) τ t c hN hτ0 ht hD' hvan
  rw [max_eq_right hτ1] at h
  have hpow : τ ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A) ≤ ‖t‖ ^ (3 * m + 4) := by
    rw [hτ, ← Real.rpow_mul ht0.le, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_ge ht0 ht1 ?_
    push_cast
    linarith
  have hpos : 0 < (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * τ ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A) := by positivity
  have hc0 : 0 ≤ C1 * (C2 * K) := by
    by_contra hneg
    have h1 : C1 * (C2 * K) * ((‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * τ ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A)) < 0 :=
      mul_neg_of_neg_of_pos (not_le.1 hneg) hpos
    have h2 := norm_nonneg (OmBlock β (m + 1) (cutPhiC τ Φ) t c)
    rw [mul_assoc] at h
    linarith
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc ‖t‖ ^ ((m + 1) ^ 2) * ‖OmBlock β (m + 1) (cutPhiC τ Φ) t c‖
      ≤ ‖t‖ ^ ((m + 1) ^ 2) * (C1 * (C2 * K) * (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ *
          τ ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ ‖t‖ ^ ((m + 1) ^ 2) * (C1 * (C2 * K) * (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * ‖t‖ ^ (3 * m + 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
    _ = C1 * (C2 * K) * (‖t‖ ^ ((m + 1) ^ 2) * ((‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * ‖t‖ ^ (3 * m + 4))) := by ring
    _ = C1 * C2 * K * ‖t‖ := by rw [pow_arith m _ ht0]; ring

theorem coef_nonneg {x c P : ℝ} (hx : 0 ≤ x) (hP : 0 < P) (h : x ≤ c * P) : 0 ≤ c := by
  by_contra hneg
  have : c * P < 0 := mul_neg_of_neg_of_pos (not_le.1 hneg) hP
  linarith

def longM (d : ℕ) (z : ℂ) (v : UT d → ℂ) : Mat d := ptLong d z * G.upper v

theorem detM_longM (m : ℕ) (z D : ℂ) (hz : z ^ (m + 2) = (-1) ^ (m + 3) * D) (v : UT (m + 1 + 1) → ℂ) :
    detM (longM (m + 1 + 1) z v) = (wMat (m + 1)).det * D := by
  have h1 : detM (longM (m + 1 + 1) z v) = (wMat (m + 1 + 1)).det * z ^ (m + 2) :=
    det_orbit.2 (m + 1 + 1) z v
  rw [h1, (det_weyl_matrix (m + 1)).1, hz]
  have h2 : (-1 : ℂ) ^ (m + 1) * (-1) ^ (m + 3) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m + 2, by ring⟩
  linear_combination ((wMat (m + 1)).det * D) * h2

theorem integrable_long (m : ℕ) (β : ℂ) (r : ℝ) (hr : 0 < r) :
    Integrable (fun v : UT (m + 1 + 1) → ℂ => (max 1 ‖r • v‖) ^ (-(((m : ℝ) + 1) * ((m : ℝ) + 4) + 1)))
      (muPi β (UT (m + 1 + 1))) := by
  have hfr : (Module.finrank ℝ (UT (m + 1 + 1) → ℂ) : ℝ) < ((m : ℝ) + 1) * ((m : ℝ) + 4) + 1 := by
    rw [finrank_pi, (dimension_count (m + 1 + 1)).1]
    have e : (((m + 1 + 1) * (m + 1 + 1 - 1) : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
      simp only [Nat.add_sub_cancel]; push_cast; ring
    rw [e]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  rw [muPi_eq]
  exact ((integrable_maxpow (volume : Measure (UT (m + 1 + 1) → ℂ)) _ hfr).comp_smul hr.ne').smul_measure_nnreal

theorem norm_omLong_le (m : ℕ) (β : ℂ) (r : ℝ) (hr : 0 < r) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Φ : Mat (m + 1 + 1) → V) (A K : ℝ) (hA : ((m : ℝ) + 1) * ((m : ℝ) + 4) + 1 ≤ A) (hK : 0 ≤ K) (z : ℂ)
    (hz : r ≤ ‖z‖)
    (hb : ∀ v, ‖Φ (longM (m + 1 + 1) z v)‖ ≤ K * min 1 (‖longM (m + 1 + 1) z v‖ ^ (-A))) :
    ‖OmLong β (m + 1) Φ z‖ ≤ K * ∫ v : UT (m + 1 + 1) → ℂ,
      (max 1 ‖r • v‖) ^ (-(((m : ℝ) + 1) * ((m : ℝ) + 4) + 1)) ∂(muPi β (UT (m + 1 + 1))) := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_long m β r hr).const_mul K)
    (Filter.Eventually.of_forall fun v => ?_)
  rw [norm_smul, (additive_character_psi β _ 0).2.1, one_mul]
  refine (hb v).trans (mul_le_mul_of_nonneg_left ?_ hK)
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  calc min 1 (‖longM (m + 1 + 1) z v‖ ^ (-A)) ≤ (max 1 ‖longM (m + 1 + 1) z v‖) ^ (-A) := min_le_maxpow A _
    _ ≤ (max 1 ‖longM (m + 1 + 1) z v‖) ^ (-(((m : ℝ) + 1) * ((m : ℝ) + 4) + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith)
    _ ≤ _ := by
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by nlinarith)
        refine max_le_max le_rfl ?_
        refine le_trans ?_ (norm_long_le z v (longM (m + 1 + 1) z v) rfl)
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hr.le]
        exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

theorem pow_arith' (m : ℕ) (x : ℝ) (hx : 0 < x) :
    x ^ ((m + 1) ^ 2) * (x ^ ((m + 1) * (m + 4)))⁻¹ = x * (x ^ (3 * m + 4))⁻¹ := by
  have h0 : x ^ (3 * m + 4) ≠ 0 := (pow_pos hx _).ne'
  calc x ^ ((m + 1) ^ 2) * (x ^ ((m + 1) * (m + 4)))⁻¹
      = (x ^ ((m + 1) ^ 2) * ((x ^ ((m + 1) * (m + 4)))⁻¹ * x ^ (3 * m + 4))) * (x ^ (3 * m + 4))⁻¹ := by
        rw [← mul_assoc, mul_assoc _ (x ^ (3 * m + 4)), mul_inv_cancel₀ h0, mul_one]
    _ = _ := by rw [pow_arith m x hx]

theorem germLargeT : GermLargeT := by
  intro m β Kc hKc h0 t₀ ht₀
  obtain ⟨CT, hCT⟩ := tailBound m β
  obtain ⟨r0, hr0, hr0'⟩ : ∃ r0 : ℝ, 0 < r0 ∧ ∀ D ∈ Kc, r0 ≤ ‖D‖ := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hKc.isClosed.isOpen_compl 0 h0
    refine ⟨ε, hε, fun D hD => ?_⟩
    by_contra hlt
    exact hball (by simpa using not_le.1 hlt : D ∈ Metric.ball (0 : ℂ) ε) hD
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, ∀ D ∈ Kc, ‖D‖ ≤ R0 := hKc.isBounded.exists_norm_le
  set r : ℝ := min 1 r0 with hr
  set R : ℝ := max 1 R0 with hR
  have hrpos : 0 < r := lt_min one_pos hr0
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_left _ _)
  set C1 : ℝ := ∫ v : UT (m + 1 + 1) → ℂ,
      (max 1 ‖r • v‖) ^ (-(((m : ℝ) + 1) * ((m : ℝ) + 4) + 1)) ∂(muPi β (UT (m + 1 + 1))) with hC1
  have hC1pos : 0 ≤ C1 := integral_nonneg fun v => by positivity
  refine ⟨CT * (t₀ ^ (3 * m + 4))⁻¹ + ((m : ℝ) + 2) * R ^ ((m + 1) ^ 2) * C1 / t₀, ?_⟩
  intro V _ _ _ Φ A K hA hΦ t c ht hD
  have ht0 : 0 < ‖t‖ := ht₀.trans_le ht
  have htne : t ≠ 0 := norm_pos_iff.1 ht0
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hbZ : ∀ Z : Mat (m + 1 + 1), detM Z = (wMat (m + 1)).det * (c * t ^ (m + 1)) →
      ‖Φ Z‖ ≤ K * min 1 (‖Z‖ ^ (-A)) := by
    intro Z hZ
    have h3 := (hΦ Z ⟨c * t ^ (m + 1), hD, hZ.symm⟩).2 0 le_rfl
    rwa [norm_iteratedFDeriv_zero] at h3
  have hΦ1 : DerivBound 0 {(wMat (m + 1)).det * (c * t ^ (m + 1))} (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ :=
    fun Z hZ => hΦ Z ⟨c * t ^ (m + 1), hD, (Set.mem_singleton_iff.1 hZ).symm⟩
  have hK : 0 ≤ K := K_nonneg (ht0.trans_le (norm_orbM_ge m t c 0)) (norm_nonneg _)
    (hbZ _ (detM_orbM (m + 1) t c 0))

  have hOm := hCT V Φ A K ‖t‖ t c hA ht0 htne hΦ1
    (fun p hp => absurd hp (not_lt.2 (norm_orbM_ge m t c p)))
  have hCK : 0 ≤ CT * K := by
    rw [mul_assoc] at hOm
    exact coef_nonneg (norm_nonneg _) (by positivity) hOm
  have hfirst : ‖((‖t‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) • OmBlock β (m + 1) Φ t c‖ ≤
      CT * (t₀ ^ (3 * m + 4))⁻¹ * K * ‖t‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hle1 : (max 1 ‖t‖) ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by linarith)
    have hinv : (‖t‖ ^ (3 * m + 4))⁻¹ ≤ (t₀ ^ (3 * m + 4))⁻¹ :=
      inv_anti₀ (pow_pos ht₀ _) (pow_le_pow_left₀ ht₀.le ht _)
    calc ‖t‖ ^ ((m + 1) ^ 2) * ‖OmBlock β (m + 1) Φ t c‖
        ≤ ‖t‖ ^ ((m + 1) ^ 2) * (CT * K * (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ *
            (max 1 ‖t‖) ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A)) := mul_le_mul_of_nonneg_left hOm (by positivity)
      _ ≤ ‖t‖ ^ ((m + 1) ^ 2) * (CT * K * (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle1 (by positivity)) (by positivity)
      _ = CT * K * (‖t‖ ^ ((m + 1) ^ 2) * (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹) := by ring
      _ = CT * K * (‖t‖ * (‖t‖ ^ (3 * m + 4))⁻¹) := by rw [pow_arith' m _ ht0]
      _ ≤ CT * K * (‖t‖ * (t₀ ^ (3 * m + 4))⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv ht0.le) hCK
      _ = _ := by ring

  have hroot : ∀ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * (c * t ^ (m + 1))),
      ‖(((‖z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * 1 * psi β (((m : ℂ) + 2) * z / t)) • OmLong β (m + 1) Φ z‖ ≤
        R ^ ((m + 1) ^ 2) * (K * C1) := by
    intro z hz
    have hz' : z ^ (m + 2) = (-1) ^ (m + 3) * (c * t ^ (m + 1)) :=
      ((root_set_characterization (m + 2) _ (by omega)).1 z).1 hz
    have hnz : ‖z‖ ^ (m + 2) = ‖c * t ^ (m + 1)‖ := by
      rw [← norm_pow, hz', norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hzr : r ≤ ‖z‖ := by
      by_contra hlt
      have h1 : ‖z‖ < r := not_le.1 hlt
      have h2 : ‖z‖ ≤ 1 := h1.le.trans (min_le_left _ _)
      have h3 : ‖z‖ ^ (m + 2) ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg _) h2 (by omega)
      have h4 := hr0' _ hD
      have h5 : r ≤ r0 := min_le_right _ _
      linarith
    have hzR : ‖z‖ ≤ R := by
      by_contra hlt
      have h1 : R < ‖z‖ := not_le.1 hlt
      have h2 : 1 ≤ ‖z‖ := (le_max_left _ _).trans h1.le
      have h3 : ‖z‖ ≤ ‖z‖ ^ (m + 2) := le_self_pow₀ h2 (by omega)
      have h4 := hR0 _ hD
      have h5 : R0 ≤ R := le_max_right _ _
      linarith
    rw [norm_smul, norm_mul, norm_mul, (additive_character_psi β _ 0).2.1, norm_one, mul_one, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzR _) ?_ (norm_nonneg _) (by positivity)
    exact norm_omLong_le m β r hrpos Φ A K hA hK z hzr fun v => hbZ _ (detM_longM m z _ hz' v)
  have hcard : ((rootSet (m + 2) ((-1) ^ (m + 3) * (c * t ^ (m + 1)))).card : ℝ) ≤ (m : ℝ) + 2 := by
    have h1 : (rootSet (m + 2) ((-1) ^ (m + 3) * (c * t ^ (m + 1)))).card ≤ m + 2 :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    exact_mod_cast h1
  have hinv1 : ‖((m : ℂ) + 2)⁻¹‖ ≤ 1 := by
    have e : ((m : ℂ) + 2) = ((m + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [norm_inv, e, Complex.norm_natCast]
    refine inv_le_one_of_one_le₀ ?_
    push_cast; linarith
  have hmain : ‖mainTerm β m (fun _ => 1) Φ t (c * t ^ (m + 1))‖ ≤
      ((m : ℝ) + 2) * R ^ ((m + 1) ^ 2) * C1 / t₀ * K * ‖t‖ := by
    unfold mainTerm
    have hB : 0 ≤ R ^ ((m + 1) ^ 2) * (K * C1) := by positivity
    calc _ ≤ 1 * (((m : ℝ) + 2) * (R ^ ((m + 1) ^ 2) * (K * C1))) := by
          rw [norm_smul]
          refine mul_le_mul hinv1 ?_ (norm_nonneg _) zero_le_one
          refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hroot).trans ?_)
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hcard hB
      _ = ((m : ℝ) + 2) * R ^ ((m + 1) ^ 2) * C1 * K * 1 := by ring
      _ ≤ ((m : ℝ) + 2) * R ^ ((m + 1) ^ 2) * C1 * K * (‖t‖ / t₀) :=
          mul_le_mul_of_nonneg_left ((one_le_div ht₀).2 ht) (by positivity)
      _ = _ := by ring
  unfold remainder
  calc _ ≤ ‖((‖t‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) • OmBlock β (m + 1) Φ t c‖ +
        ‖mainTerm β m (fun _ => 1) Φ t (c * t ^ (m + 1))‖ := norm_sub_le _ _
    _ ≤ CT * (t₀ ^ (3 * m + 4))⁻¹ * K * ‖t‖ + ((m : ℝ) + 2) * R ^ ((m + 1) ^ 2) * C1 / t₀ * K * ‖t‖ :=
        add_le_add hfirst hmain
    _ = _ := by ring

end Formalism.FourierDecayAlt.P.OrbitTailEstimates

namespace Formalism.FourierDecayAlt.P

theorem tailBound_statement : Formalism.FourierDecayAlt.G.TailBound := OrbitTailEstimates.tailBound

theorem tail_estimate_of_bound : Formalism.FourierDecayAlt.G.TailStepOfBound := OrbitTailEstimates.tailStepOfBound

theorem germ_large_parameter : Formalism.FourierDecayAlt.G.GermLargeT := OrbitTailEstimates.germLargeT

end Formalism.FourierDecayAlt.P
