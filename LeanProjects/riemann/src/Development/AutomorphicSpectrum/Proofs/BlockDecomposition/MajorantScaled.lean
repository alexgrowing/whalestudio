import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelUniformBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralMajorantFiberBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantLeSumSwapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralMajorantLePowNegStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDetInvMulMajorantStatement

noncomputable section

open MeasureTheory Matrix Ad3.K.LC Ad3.K.LC.B

namespace GlobalTheory.CompanionTheory.MajC

theorem L_eta : ∀ h : M22, (Matrix.of h).det ≠ 0 → 0 < col h ∧ ‖eta h‖ = col h / dt h := by
  intro h hdet
  have hn : ∀ w : Fin 2 → ℂ, ‖w‖ = max ‖w 0‖ ‖w 1‖ := by
    intro w
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_)
      (max_le (norm_le_pi_norm w 0) (norm_le_pi_norm w 1))
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hD : 0 < dt h := norm_pos_iff.mpr hdet
  have he0 : eta h 0 = (Matrix.of h).det⁻¹ * (-h 1 0) := by
    simp [eta, Matrix.inv_def, Matrix.adjugate_fin_two]
  have he1 : eta h 1 = (Matrix.of h).det⁻¹ * h 0 0 := by
    simp [eta, Matrix.inv_def, Matrix.adjugate_fin_two]
  constructor
  · by_contra hc
    have hc0 : col h = 0 := le_antisymm (not_lt.mp hc) (le_max_of_le_left (norm_nonneg _))
    have h0 : h 0 0 = 0 := by
      have : ‖h 0 0‖ ≤ 0 := hc0 ▸ le_max_left _ _
      exact norm_le_zero_iff.mp this
    have h1 : h 1 0 = 0 := by
      have : ‖h 1 0‖ ≤ 0 := hc0 ▸ le_max_right _ _
      exact norm_le_zero_iff.mp this
    exact hdet (by simp [Matrix.det_fin_two, h0, h1])
  · rw [hn, he0, he1, norm_mul, norm_mul, norm_neg, norm_inv, ← mul_max_of_nonneg _ _ (by positivity), col, dt,
      max_comm]
    field_simp

theorem L_swp : ∀ f : M22 → ENNReal, ∫⁻ h : M22, f (swp h) = ∫⁻ h : M22, f h := by
  intro f
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Fin 2 → ℂ)
  have he : MeasurePreserving e volume volume := volume_preserving_piFinTwo _
  let s : M22 ≃ᵐ M22 := e.trans (MeasurableEquiv.prodComm.trans e.symm)
  have hs : MeasurePreserving s volume volume := by
    have hw : MeasurePreserving (Prod.swap : (Fin 2 → ℂ) × (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) volume volume :=
      Measure.measurePreserving_swap
    exact ((he.symm e).comp hw).comp he
  have hsw : ∀ h, s h = swp h := by
    intro h
    funext i
    fin_cases i <;> rfl
  have := hs.lintegral_comp_emb s.measurableEmbedding f
  simpa only [hsw] using this

theorem L_measgm : ∀ (ε β : ℝ) (m : ℕ), Measurable (gm ε β m) := by
  intro ε β m
  have h00 : Measurable fun h : M22 => h 0 0 := (measurable_pi_apply 0).comp (measurable_pi_apply 0)
  have h01 : Measurable fun h : M22 => h 0 1 := (measurable_pi_apply 1).comp (measurable_pi_apply 0)
  have h10 : Measurable fun h : M22 => h 1 0 := (measurable_pi_apply 0).comp (measurable_pi_apply 1)
  have h11 : Measurable fun h : M22 => h 1 1 := (measurable_pi_apply 1).comp (measurable_pi_apply 1)
  have hz : Measurable fun h : M22 => h 1 1 - h 1 0 / h 0 0 * h 0 1 :=
    h11.sub ((h10.div h00).mul h01)
  have hk : Measurable (kern ε β) := by
    unfold kern
    fun_prop
  have hset : MeasurableSet {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖ ∧ h 0 0 ≠ 0} :=
    (measurableSet_le h10.norm h00.norm).inter (h00 (measurableSet_singleton 0).compl)
  unfold gm
  refine Measurable.ite hset ?_ measurable_const
  have := hk.comp hz
  simp only [Function.comp_def] at this
  exact ((((measurable_const.mul (h00.norm.pow_const _)).mul
    ((measurable_const.add h00.norm).pow_const m).inv).mul
    ((measurable_const.add h01.norm).pow_const m).inv).mul this)

theorem hm_int (ε : ℝ) (hε : 0 < ε) (m : ℕ) (h3 : 3 ≤ m) (hm2 : 2 * ε ≤ m) (K : ℝ) (hK : 0 ≤ K)
    (hk : ∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern ε T₀ z) ≤ ENNReal.ofReal K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 * m ≤ N → ∀ β : ℝ, 0 < β →
      ∫⁻ h : M22, ENNReal.ofReal (hm ε N β h) ≤ ENNReal.ofReal (C * β ^ (-ε)) := by
  obtain ⟨C, hC, hg⟩ := GlobalTheory.T.lintegral_majorant_le_pow_neg ε K m hε hK hk h3 hm2
  refine ⟨2 * C, by positivity, fun N hN β hβ => ?_⟩
  have hg0 : ∀ h, 0 ≤ gm ε β m h := by
    intro h
    unfold gm
    split_ifs
    · unfold kern
      positivity
    · exact le_rfl
  have hmeas : Measurable (gm ε β m) := L_measgm ε β m
  calc ∫⁻ h : M22, ENNReal.ofReal (hm ε N β h)
      ≤ ∫⁻ h : M22, (ENNReal.ofReal (gm ε β m h) + ENNReal.ofReal (gm ε β m (swp h))) := by
        refine lintegral_mono fun h => ?_
        rw [← ENNReal.ofReal_add (hg0 _) (hg0 _)]
        exact ENNReal.ofReal_le_ofReal (GlobalTheory.T.majorant_le_sum_swap ε β m N hε hβ hm2 hN h)
    _ = (∫⁻ h : M22, ENNReal.ofReal (gm ε β m h)) + ∫⁻ h : M22, ENNReal.ofReal (gm ε β m (swp h)) :=
        lintegral_add_left hmeas.ennreal_ofReal _
    _ = (∫⁻ h : M22, ENNReal.ofReal (gm ε β m h)) + ∫⁻ h : M22, ENNReal.ofReal (gm ε β m h) := by
        rw [L_swp (fun h => ENNReal.ofReal (gm ε β m h))]
    _ ≤ ENNReal.ofReal (C * β ^ (-ε)) + ENNReal.ofReal (C * β ^ (-ε)) := add_le_add (hg β hβ) (hg β hβ)
    _ = ENNReal.ofReal (2 * C * β ^ (-ε)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

theorem main : Ad3.K.LC.B.MajScaled := by
  intro ε hε
  obtain ⟨K1, hK1, hk1⟩ := GlobalTheory.T.lintegral_kernel_uniform_bound ε hε
  obtain ⟨K2, hK2, hk2⟩ := GlobalTheory.T.lintegral_kernel_uniform_bound (2 * ε) (by positivity)
  set m : ℕ := max 3 ⌈2 * ε⌉₊ with hmdef
  have h3 : 3 ≤ m := le_max_left _ _
  have hm2 : 2 * ε ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  obtain ⟨C, hC, hH⟩ := hm_int ε hε m h3 hm2 K1 hK1 hk1
  refine ⟨2 * m, fun N hN => ⟨K2 * C, fun a b ha hb => ?_⟩⟩
  have hNε : 2 * ε ≤ N := by
    have : (2 * m : ℝ) ≤ N := by exact_mod_cast hN
    have h0 : (0 : ℝ) ≤ m := by positivity
    linarith
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hB : 0 < ‖b‖ := norm_pos_iff.mpr hb
  set f : M22 × ℂ → ℝ := fun p => (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 a b with hf
  have hfm : Measurable f := GlobalTheory.T.measurable_det_inv_mul_majorant N a b
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    simp only [hf, jm]
    positivity
  have hper : ∀ h : M22, ∫⁻ t : ℂ, ENNReal.ofReal (f (h, t)) ≤
      ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ENNReal.ofReal (hm ε N ‖b‖ h) := by
    intro h
    by_cases hdet : (Matrix.of h).det = 0
    · simp [hf, hdet]
    have hD : 0 < dt h := norm_pos_iff.mpr hdet
    obtain ⟨hc, hE⟩ := L_eta h hdet
    have hE0 : 0 < ‖eta h‖ := by rw [hE]; positivity
    have hfe : ∀ t : ℂ, ENNReal.ofReal (f (h, t)) =
        ENNReal.ofReal ((dt h ^ 2)⁻¹) * ENNReal.ofReal (jm N h t a b) := by
      intro t
      rw [← ENNReal.ofReal_mul (by positivity)]
      rfl
    simp_rw [hfe]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right (GlobalTheory.T.lintegral_majorant_fiber_bound ε K2 hε hK2 hk2 N hNε h a b ha hD hE0) _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hpow : (dt h ^ 2)⁻¹ * dt h ^ (-2 + ε) * ‖eta h‖ ^ (-2 + 2 * ε) =
        dt h ^ (-(2 + ε)) * col h ^ (-2 + 2 * ε) := by
      rw [hE, Real.div_rpow hc.le hD.le, Real.rpow_add hD, Real.rpow_neg hD.le (2 + ε), Real.rpow_add hD,
        Real.rpow_add hD, two_mul ε, Real.rpow_add hD ε ε, Real.rpow_neg hD.le 2, Real.rpow_two]
      have hP := Real.rpow_pos_of_pos hD ε
      field_simp
    simp only [hm]
    rw [← hE]
    calc _ = K2 * ‖a‖ ^ (-ε) * ((dt h ^ 2)⁻¹ * dt h ^ (-2 + ε) * ‖eta h‖ ^ (-2 + 2 * ε)) * ((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ := by ring
      _ = _ := by rw [hpow]; ring
  have hlin : ∫⁻ p, ENNReal.ofReal (f p) ≤ ENNReal.ofReal (K2 * C * (‖a‖ * ‖b‖) ^ (-ε)) := by
    rw [Measure.volume_eq_prod, lintegral_prod _ hfm.ennreal_ofReal.aemeasurable]
    calc ∫⁻ h : M22, ∫⁻ t : ℂ, ENNReal.ofReal (f (h, t))
        ≤ ∫⁻ h : M22, ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ENNReal.ofReal (hm ε N ‖b‖ h) :=
          lintegral_mono hper
      _ = ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ∫⁻ h : M22, ENNReal.ofReal (hm ε N ‖b‖ h) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ENNReal.ofReal (C * ‖b‖ ^ (-ε)) :=
          mul_le_mul_right (hH N hN ‖b‖ hB) _
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), Real.mul_rpow hA.le hB.le]
          congr 1
          ring
  have hint : Integrable f := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

end GlobalTheory.CompanionTheory.MajC
