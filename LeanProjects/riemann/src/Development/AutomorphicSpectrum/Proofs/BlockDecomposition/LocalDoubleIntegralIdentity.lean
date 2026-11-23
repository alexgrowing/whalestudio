import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaRegionMeasureBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerIwasawaGrowthBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricSumBelowThresholdStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaSumMeasureEstimateStatement

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.LFGInt2

theorem modulus_det_iwasawa_inv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (x : F) (a b : Fˣ) (κ : GL (Fin 2) F), κ ∈ GLnLocal.integralGL F 2 → (modulus ((Matrix.GeneralLinearGroup.det (Ad3.uni2 x * Ad3.dg2 a b * κ)⁻¹ : Fˣ) : F) : ℝ) = ((modulus (a : F) : ℝ) * (modulus (b : F) : ℝ))⁻¹ := by
  intro F _ _ _ _ x a b κ hκ
  have hκ1 : modulus ((Matrix.GeneralLinearGroup.det κ : Fˣ) : F) = 1 := by
    obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hκ
    have key : ∀ g : GL (Fin 2) F, (∀ i j, g i j ∈ 𝒪[F]) →
        modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ≤ 1 := by
      intro g hg
      rw [modulus_le_one_iff, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      exact sub_mem (mul_mem (hg 0 0) (hg 1 1)) (mul_mem (hg 0 1) (hg 1 0))
    have a' := key κ h1
    have b' := key κ⁻¹ h2
    rw [map_inv, Units.val_inv_eq_inv_val, modulus_inv] at b'
    have hpos := modulus_pos (Matrix.GeneralLinearGroup.det κ : Fˣ).ne_zero
    exact le_antisymm a' ((inv_le_one₀ hpos).1 b')
  have hd1 : Matrix.GeneralLinearGroup.det (Ad3.uni2 x) = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Ad3.uni2, Matrix.det_fin_two]
  have hd2 : Matrix.GeneralLinearGroup.det (Ad3.dg2 a b) = a * b := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Ad3.dg2, Matrix.det_fin_two]
  rw [map_inv, map_mul, map_mul, hd1, hd2, one_mul, Units.val_inv_eq_inv_val, modulus_inv, Units.val_mul,
    modulus_mul, hκ1, mul_one, Units.val_mul, modulus_mul]
  push_cast
  rfl

open Ad3 Ad3.LFS in

theorem gInt2 : Ad3.LFS.GInt2 := by
  intro F _ _ _ _ _ _ ψ hψ ν hν V' H W' hW' R
  classical
  obtain ⟨C, B, hCB⟩ := H.bound W' hW' (1 / 4) (by norm_num)
  set q : ℝ := (residueCard F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast (one_lt_residueCard (K := F))
  have hq0 : 0 < q := by linarith
  obtain ⟨L₀, hL₀⟩ := pow_unbounded_of_one_lt R hq
  set L : ℤ := (L₀ : ℤ) with hLdef
  have hRL : R ≤ q ^ L := by rw [hLdef, zpow_natCast]; exact hL₀.le
  haveI hμ : (hG ψ).IsHaarMeasure := by unfold hG; infer_instance
  haveI hinv : (hG ψ).IsInvInvariant := ⟨Measures.inv_eq_self_GL F 2 (hG ψ)⟩
  set Kμ : ℝ≥0∞ := hG ψ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) with hKμ
  have hKfin : Kμ ≠ ∞ := (GLnLocal.isCompact_integralGL F 2).measure_lt_top.ne
  set C₁ : ℝ := max C 0 with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  have hbound : ∀ (a : Fˣ), ∀ κ ∈ GLnLocal.integralGL F 2,
      ‖W' (dg2 a 1 * κ)‖ ≤ C₁ * (modulus (a : F) : ℝ) ^ (1 / 4 : ℝ) := by
    intro a κ hκ
    have h := (hCB a κ hκ).1
    rw [show (1 / 2 - 1 / 4 : ℝ) = 1 / 4 by norm_num] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hpsi : ∀ x g, W' (uni2 x * g) = (ψ x : ℂ) * W' g := H.psi W' hW'
  have hcen : ∀ (a : Fˣ) g, W' (dg2 a a * g) = W' g := by
    intro a g
    rw [H.cen W' hW']
    simp
  obtain ⟨U, hU⟩ := H.smooth W' hW'
  have hWc : Continuous W' := by
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨{x | g⁻¹ * x ∈ U}, U.isOpen.preimage (continuous_const.mul continuous_id), by simp [U.one_mem],
      fun x hx => ?_⟩
    have := hU g _ hx
    simpa using this
  have hval : Continuous fun k : GL (Fin 2) F => (k : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have hmod : Continuous fun x : F => (modulus x : ℝ) := NNReal.continuous_coe.comp continuous_modulus
  have hdet : Continuous fun k : GL (Fin 2) F => (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) := by
    have : Continuous fun k : GL (Fin 2) F => ((GeneralLinearGroup.det k : Fˣ) : F) := by
      simpa using hval.matrix_det
    exact hmod.comp this
  have homc : ∀ t : Fˣ, IsClosed (om R t : Set (GL (Fin 2) F)) := by
    intro t
    have e : (om R t : Set (GL (Fin 2) F)) = (⋂ i, ⋂ j, {k : GL (Fin 2) F | (modulus ((k : Matrix (Fin 2) (Fin 2) F) i j) : ℝ) ≤ R}) ∩
        ⋂ j, {k : GL (Fin 2) F | (modulus ((t : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) : ℝ) ≤ R} := by
      ext k
      simp [om]
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (hmod.comp (hval.matrix_elem i j)) continuous_const) (isClosed_iInter fun j =>
      isClosed_le (hmod.comp (continuous_const.mul ((hval.comp continuous_inv).matrix_elem 1 j))) continuous_const)
  set r : ℝ := q ^ (-(1 / 4) : ℝ) with hr
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)
  set D : ℝ := 1 - r with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hqL : 0 < q ^ L := zpow_pos hq0 L
  refine ⟨C₁ * q ^ L * ((q ^ L) ^ (1 / 4 : ℝ) / D) ^ 2 * Kμ.toReal, fun t₁ t₂ => ?_⟩
  set τ : ℝ := (modulus (t₂ : F) : ℝ) with hτdef
  have hτ : 0 < τ := by exact_mod_cast modulus_pos t₂.ne_zero
  set σ : ℝ := (modulus (t₁ : F) : ℝ) with hσdef
  have hσ : 0 < σ := by exact_mod_cast modulus_pos t₁.ne_zero
  set f : GL (Fin 2) F → ℝ := (om R t₂).indicator fun k =>
    ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => Set.indicator_nonneg (fun _ _ => by positivity) k
  have hfm : Measurable f := by
    refine Measurable.indicator (Continuous.measurable ?_) (homc t₂).measurableSet
    exact (hWc.comp (continuous_const.mul continuous_inv)).norm.mul
      (hdet.rpow_const fun _ => Or.inr (by norm_num))
  set A : ℝ := C₁ * (σ / τ) ^ (1 / 4 : ℝ) with hA
  have hA0 : 0 ≤ A := by positivity
  set T₁r : ℝ := (q ^ L) ^ (1 / 4 : ℝ) / D with hT₁r
  set T₂r : ℝ := (q ^ L / τ) ^ (1 / 4 : ℝ) / D with hT₂r
  have hT₁ : (∑' m : ℤ, (if m ≤ L then ENNReal.ofReal (q ^ ((m : ℝ) / 4)) else 0)) ≤ ENNReal.ofReal T₁r := by
    have h := GlobalTheory.T.geometric_sum_below_threshold q (1 / 4) (q ^ L) hq (by norm_num) hqL
    refine le_of_eq_of_le (tsum_congr fun m => ?_) h
    simp only [zpow_le_zpow_iff_right₀ hq]
    rw [show (m : ℝ) / 4 = 1 / 4 * (m : ℝ) by ring]
  have hT₂ : (∑' n : ℤ, (if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) else 0)) ≤ ENNReal.ofReal T₂r := by
    have h := GlobalTheory.T.geometric_sum_below_threshold q (1 / 4) (q ^ L / τ) hq (by norm_num) (div_pos hqL hτ)
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine le_of_eq_of_le (tsum_congr fun m => ?_) h
    simp only [Equiv.neg_apply, neg_neg, Int.cast_neg]
    have e : τ * q ^ m ≤ q ^ L ↔ q ^ m ≤ q ^ L / τ := by rw [le_div_iff₀ hτ, mul_comm]
    simp only [e]
    rw [show (m : ℝ) / 4 = 1 / 4 * (m : ℝ) by ring]
  set S : ℤ → ℤ → Set (GL (Fin 2) F) := fun m n => {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ q ^ (L - m) ∧
    ∃ κ ∈ GLnLocal.integralGL F 2, g = uni2 x * dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} with hS
  set Φ : GL (Fin 2) F → ℝ≥0∞ := fun g => ENNReal.ofReal (f g⁻¹) with hΦ
  have hcov : ∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L ∧ y ∈ S m n ∧
      Φ y ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) := by
    intro g hg
    have hom : g⁻¹ ∈ om R t₂ := by
      by_contra h
      exact hg (by simp [hΦ, hf, h])
    obtain ⟨x, m, n, κ, hκ, rfl⟩ := GlobalTheory.T.iwasawa_decomposition_gl_two_holds F g
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.iwasawa_coordinates_bounded_region F x m n L κ R t₂ hκ hRL hom
    refine ⟨m, n, h1, h2, h4, ⟨x, h3, κ, hκ, rfl⟩, ENNReal.ofReal_le_ofReal ?_⟩
    rw [hf, Set.indicator_of_mem hom, inv_inv]
    have hw := GlobalTheory.T.whittaker_iwasawa_growth_bound F ψ W' C₁ hpsi hcen hbound t₁ t₂ (unifUnit F ^ m) (unifUnit F ^ n) x κ hκ
    have hu : ∀ k : ℤ, (modulus (((unifUnit F ^ k : Fˣ)) : F) : ℝ) = q ^ (-(k : ℝ)) := by
      intro k
      rw [modulus_of_ne_zero (Units.ne_zero _), ord_unifUnit_zpow, NNReal.coe_zpow, NNReal.coe_natCast,
        ← Real.rpow_intCast]
      push_cast
      rfl
    have hM : (modulus ((t₁ * unifUnit F ^ m * (t₂ * unifUnit F ^ n)⁻¹ : Fˣ) : F) : ℝ) =
        (σ / τ) * q ^ ((n : ℝ) - m) := by
      rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mul, modulus_mul, modulus_mul,
        modulus_inv, modulus_mul]
      simp only [NNReal.coe_mul, NNReal.coe_inv]
      rw [hu, hu, ← hσdef, ← hτdef, sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_neg hq0.le (m : ℝ),
        Real.rpow_neg hq0.le (n : ℝ)]
      have := (Real.rpow_pos_of_pos hq0 (m : ℝ)).ne'
      have := (Real.rpow_pos_of_pos hq0 (n : ℝ)).ne'
      field_simp
    have hdetg := modulus_det_iwasawa_inv F x (unifUnit F ^ m) (unifUnit F ^ n) κ hκ
    rw [hM] at hw
    rw [hdetg, hu, hu, mul_inv, ← Real.rpow_neg hq0.le, ← Real.rpow_neg hq0.le, neg_neg, neg_neg,
      ← Real.rpow_add hq0, ← Real.rpow_mul hq0.le]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hq0.le] at hw
    have e1 : ((n : ℝ) - m) * (1 / 4) = ((n : ℝ) - m) / 4 := by ring
    have e2 : ((m : ℝ) + n) * (1 / 2) = ((m : ℝ) + n) / 2 := by ring
    rw [e1] at hw
    rw [e2, hA, mul_assoc C₁]
    exact mul_le_mul_of_nonneg_right hw (by positivity)
  have hmain := GlobalTheory.T.iwasawa_sum_measure_estimate (hG ψ) q A τ L Kμ _ _ S Φ hq hA0 hτ
    (fun m n => (GlobalTheory.T.iwasawa_region_measure_bound F (hG ψ) m n L).1.measurableSet) (fun m n hn => (GlobalTheory.T.iwasawa_region_measure_bound F (hG ψ) m n L).2 hn)
    hT₁ hT₂ hcov
  have hinvl : ∫⁻ k, ENNReal.ofReal (f k) ∂hG ψ = ∫⁻ g, Φ g ∂hG ψ :=
    ((Measure.measurePreserving_inv (hG ψ)).lintegral_comp hfm.ennreal_ofReal).symm
  set Rr : ℝ := C₁ * q ^ L * ((q ^ L) ^ (1 / 4 : ℝ) / D) ^ 2 * Kμ.toReal * σ ^ (1 / 4 : ℝ) * τ ^ (-(1 / 2) : ℝ) with hRr
  have hRr0 : 0 ≤ Rr := by positivity
  have hfin : ∫⁻ k, ENNReal.ofReal (f k) ∂hG ψ ≤ ENNReal.ofReal Rr := by
    rw [hinvl]
    refine hmain.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hKfin, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hw0 : 0 < τ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hτ _
    have hw2 : τ ^ (-(1 / 2) : ℝ) = ((τ ^ (1 / 4 : ℝ)) ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le, ← Real.rpow_neg hτ.le]
      norm_num
    rw [hRr, hA, hT₁r, hT₂r, hw2, Real.div_rpow hσ.le hτ.le, Real.div_rpow hqL.le hτ.le]
    field_simp
  refine ⟨⟨hfm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)]
    exact hfin.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hRr0 hfin

end GlobalTheory.CompanionTheory.LFGInt2
