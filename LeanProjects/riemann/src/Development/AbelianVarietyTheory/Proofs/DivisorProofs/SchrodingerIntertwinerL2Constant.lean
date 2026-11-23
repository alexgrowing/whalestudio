import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalIntegralCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerRepSchwartzPolynomialBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffContinuousRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOrthogonalityRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormConstMulInnerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerRepUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoInvariantFormConstMulInnerStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.RealWeil
open scoped Matrix ENNReal SchwartzMap

namespace GlobalTheory.SvNForm

theorem sympl_neg_self {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) : sympl w (-w) = 0 := by
  have h1 : pPart (-w) = -pPart w := rfl
  have h2 : qPart (-w) = -qPart w := rfl
  simp only [sympl, h1, h2, inner_neg_right, real_inner_comm (pPart w) (qPart w)]
  ring

theorem rhoFun_neg_cancel {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℂ) :
    rhoFun w (rhoFun (-w) u) = u := by
  rw [rhoFun_rhoFun, sympl_neg_self, add_neg_cancel, rhoFun_zero]
  simp

theorem step (n : ℕ) (B : Sch (Fin n) → Sch (Fin n) → ℂ)
    (hB : ∀ h', ∃ L : Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h)
    (f f' g g' : Sch (Fin n)) (G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n)) (hGc : Continuous G)
    (hG : ∀ w, ⇑(G w) = rhoFun w ⇑f)
    (hGb : ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N) :
    (∫ x, f x * starRingEnd ℂ (g x)) * B g' f' =
      ∫ w, starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * B (G w) f' := by
  obtain ⟨L, hL⟩ := hB f'
  set ip : ℂ := ∫ x, f x * starRingEnd ℂ (g x) with hip
  set c : (Fin n ⊕ Fin n → ℝ) → ℂ := fun w => starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) with hc
  have hcc : Continuous c := Complex.continuous_conj.comp (GlobalTheory.T.matrix_coeff_continuous_rapid_decay n g g').1
  have hint : ∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) := by
    intro k m
    obtain ⟨C, N, hC⟩ := hGb k m
    set d : ℕ := Module.finrank ℝ (Fin n ⊕ Fin n → ℝ)
    obtain ⟨C', hC'⟩ := (GlobalTheory.T.matrix_coeff_continuous_rapid_decay n g g').2 (N + (d + 1))
    have hsc : Continuous fun w => SchwartzMap.seminorm ℂ k m (G w) :=
      ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin n)) ℂ).continuous_seminorm (k, m)).comp hGc
    have hI : Integrable (fun w : Fin n ⊕ Fin n → ℝ => (1 + ‖w‖) ^ (-((d + 1 : ℕ) : ℝ))) :=
      integrable_one_add_norm (by push_cast; linarith)
    refine (hI.const_mul (C' * |C|)).mono' ((hcc.norm.mul hsc).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => ?_)
    have hpos : 0 < 1 + ‖w‖ := by positivity
    have e1 : ‖c w‖ = ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖ := by simp [hc]
    have h1 := hC' w
    have h2 := hC w
    have hs0 : 0 ≤ SchwartzMap.seminorm ℂ k m (G w) := apply_nonneg _ _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hs0, e1]
    have hrp : (1 + ‖w‖) ^ (-((d + 1 : ℕ) : ℝ)) = ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    rw [hrp]
    set M := ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖
    have hM : 0 ≤ M := norm_nonneg _
    have hA : (0:ℝ) < (1 + ‖w‖) ^ N := by positivity
    have hB' : (0:ℝ) < (1 + ‖w‖) ^ (d + 1) := by positivity
    have h3 : SchwartzMap.seminorm ℂ k m (G w) ≤ |C| * (1 + ‖w‖) ^ N :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hA.le)
    rw [pow_add] at h1
    calc M * SchwartzMap.seminorm ℂ k m (G w) ≤ M * (|C| * (1 + ‖w‖) ^ N) := mul_le_mul_of_nonneg_left h3 hM
      _ = |C| * (M * ((1 + ‖w‖) ^ N * (1 + ‖w‖) ^ (d + 1))) * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
          field_simp
      _ ≤ |C| * C' * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
          gcongr
      _ = C' * |C| * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by ring
  have hpt : ∀ x, (ip • g') x = ∫ w, c w * G w x := by
    intro x
    simp only [SchwartzMap.smul_apply, smul_eq_mul, hc, hG]
    rw [GlobalTheory.T.schrodinger_orthogonality_relation n f g g' x]
  have key := GlobalTheory.T.schwartz_functional_integral_comm (Fin n ⊕ Fin n → ℝ) volume n L G c (ip • g') hGc hcc hint hpt
  calc ip * B g' f' = B (ip • g') f' := by rw [hL, hL, map_smul, smul_eq_mul]
    _ = ∫ w, c w * L (G w) := by rw [hL]; exact key
    _ = ∫ w, c w * B (G w) f' := by simp only [hL]

theorem core : ∀ (n : ℕ) (B : GlobalTheory.RealWeil.Sch (Fin n) → GlobalTheory.RealWeil.Sch (Fin n) → ℂ),
    (∀ h', ∃ L : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h) →
    (∀ h h', B h' h = starRingEnd ℂ (B h h')) → (∀ h, 0 ≤ (B h h).re) →
    (∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑h' → B g g' = B h h') →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x) := by
  intro n B hB hherm hpos hinv
  refine GlobalTheory.T.hermitian_form_const_mul_inner n B hherm hpos fun f f' g g' => ?_
  obtain ⟨G, hGc, hG, hGb⟩ := GlobalTheory.T.schrodinger_rep_schwartz_polynomial_bound n f
  obtain ⟨G', hG'c, hG', hG'b⟩ := GlobalTheory.T.schrodinger_rep_schwartz_polynomial_bound n f'
  have s1 := step n B hB f f' g g' G hGc hG hGb
  have s2 := step n B hB f' f g' g G' hG'c hG' hG'b
  set mc : Sch (Fin n) → Sch (Fin n) → (Fin n ⊕ Fin n → ℝ) → ℂ :=
    fun u v w => ∫ t, rhoFun w ⇑u t * starRingEnd ℂ (v t) with hmc
  have pw : ∀ w, starRingEnd ℂ (mc g g' w) * B (G w) f' = mc g' g (-w) * starRingEnd ℂ (B (G' (-w)) f) := by
    intro w
    have e1 : B (G w) f' = B f (G' (-w)) :=
      hinv w f (G' (-w)) (G w) f' (hG w) (by rw [hG' (-w), rhoFun_neg_cancel])
    have e2 : mc g g' w = ∫ t, g t * starRingEnd ℂ (rhoFun (-w) ⇑g' t) := by
      simp only [hmc]
      conv_lhs => rw [← rhoFun_neg_cancel w ⇑g']
      exact GlobalTheory.T.schrodinger_rep_unitary n w ⇑g (rhoFun (-w) ⇑g')
    rw [e1, hherm, e2, ← integral_conj]
    simp only [hmc, map_mul, Complex.conj_conj]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [mul_comm]
  rw [s1]
  have e3 : (∫ x, g' x * starRingEnd ℂ (f' x)) * B f g =
      starRingEnd ℂ ((∫ x, f' x * starRingEnd ℂ (g' x)) * B g f) := by
    rw [map_mul, ← integral_conj, hherm g f]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [mul_comm]
  simp only [hmc] at pw
  rw [e3, s2, ← integral_conj]
  simp only [pw]
  have hneg := integral_neg_eq_self (fun w => (∫ t, rhoFun w ⇑g' t * starRingEnd ℂ (g t)) *
    starRingEnd ℂ (B (G' w) f)) (volume : Measure (Fin n ⊕ Fin n → ℝ))
  rw [hneg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp [map_mul]

theorem schrodinger_intertwiner_l2_const : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := GlobalTheory.T.rho_invariant_form_const_mul_inner core

end GlobalTheory.SvNForm
