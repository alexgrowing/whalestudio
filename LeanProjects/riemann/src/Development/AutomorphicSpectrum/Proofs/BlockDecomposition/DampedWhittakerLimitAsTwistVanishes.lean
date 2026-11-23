import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGaugeBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLinearity

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.DampedWhittakerLimit

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_mp (s : ℂ) : Continuous fun h : Fˣ => mp h s := by
  have hc : Continuous fun h : Fˣ => (((modulus (h : F) : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))
  simp only [mp]
  refine hc.cpow continuous_const fun h => ?_
  have h0 : (0 : ℝ) < (modulus (h : F) : ℝ) := by exact_mod_cast modulus_pos h.ne_zero
  exact Complex.ofReal_mem_slitPlane.2 h0

theorem tendsto_mp (a : Fˣ) {δ : ℕ → ℝ} (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => mp a (δ n)) Filter.atTop (nhds 1) := by
  have h0 : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  have h1 : (((modulus (a : F) : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have hc : Continuous fun s : ℂ => mp a s := by
    simp only [mp]
    exact continuous_id.const_cpow (Or.inl h1)
  have hδ' : Filter.Tendsto (fun n => ((δ n : ℝ) : ℂ)) Filter.atTop (nhds ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp hδ
  have := (hc.tendsto ((0 : ℝ) : ℂ)).comp hδ'
  simpa [mp, Function.comp_def] using this

theorem inv_rpow_le {m Q δ : ℝ} (hm : 0 < m) (h1 : m ≤ Q) (h2 : m⁻¹ ≤ Q) (hδ : |δ| ≤ 1) :
    (m ^ δ)⁻¹ ≤ Q := by
  have hQ : 0 < Q := hm.trans_le h1
  have hl1 : Real.log m ≤ Real.log Q := Real.log_le_log hm h1
  have hl2 : -Real.log m ≤ Real.log Q := by
    rw [← Real.log_inv]
    exact Real.log_le_log (inv_pos.2 hm) h2
  have hQ1 : 0 ≤ Real.log Q := by linarith
  have habs : |Real.log m| ≤ Real.log Q := abs_le.2 ⟨by linarith, hl1⟩
  rw [← Real.rpow_neg hm.le, Real.rpow_def_of_pos hm]
  calc Real.exp (Real.log m * -δ) ≤ Real.exp (Real.log Q) := by
        refine Real.exp_le_exp.2 ?_
        calc Real.log m * -δ ≤ |Real.log m * -δ| := le_abs_self _
          _ = |Real.log m| * |δ| := by rw [abs_mul, abs_neg]
          _ ≤ Real.log Q * 1 := mul_le_mul habs hδ (abs_nonneg _) hQ1
          _ = Real.log Q := mul_one _
    _ = Q := Real.exp_log hQ

end

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem tendsto_outer {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ GodementSectionLocal.schwartzBruhat2 F)
    {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (μ : Measure F) [μ.IsAddHaarMeasure]
    {ν : Fˣ →* ℂˣ} (hν : IsUnit1 ν) {ν' : ℕ → Fˣ →* ℂˣ} {δ : ℕ → ℝ}
    (hν' : ∀ n a, ((ν' n a : ℂˣ) : ℂ) = ((ν a : ℂˣ) : ℂ) * mp a (δ n))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ h : Fˣ, (((ν' n h)⁻¹ * (ν' n)⁻¹ h : ℂˣ) : ℂ) * mp h 1 *
        ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂μ ∂multHaar F) Filter.atTop
      (nhds (∫ h : Fˣ, (((ν h)⁻¹ * ν⁻¹ h : ℂˣ) : ℂ) * mp h 1 *
        ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂μ ∂multHaar F)) := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hψ1 (DFunLike.ext _ _ fun a => (hall a).trans (AddChar.one_apply a).symm)
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one ψ)
  obtain ⟨N, M, -, hN, hM⟩ := GodementSectionLocal.exists_invariant_of_mem_schwartzBruhat2 hΦ
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖Φ x‖ ≤ C := hΦ.2.exists_bound_of_continuous hΦ.1.continuous
  set B : ℤ := N - ord x₀ with hB
  set S : Set Fˣ := ⋃ k ∈ Set.Ico M B, ordShell F k with hS
  have hSm : MeasurableSet S :=
    (Set.finite_Ico M B).measurableSet_biUnion fun k _ => measurableSet_ordShell k
  have hSf : multHaar F S ≠ ⊤ :=
    (measure_biUnion_lt_top (Set.finite_Ico M B) fun k _ => by
      rw [multHaar_ordShell]; exact ENNReal.one_lt_top).ne
  have hmem : ∀ h : Fˣ, h ∈ S ↔ M ≤ ord (h : F) ∧ ord (h : F) < B := by
    intro h
    simp [hS, mem_ordShell]
  set I : Fˣ → ℂ := fun h => ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂μ with hIdef
  have hzero : ∀ h : Fˣ, h ∉ S → I h = 0 := by
    intro h hh
    rw [hmem, not_and_or, not_le, not_lt] at hh
    rcases hh with hh | hh
    · exact GlobalTheory.CompanionTheory.WhitLin.inner_eq_zero_of_lt μ hM h hh
    · refine GlobalTheory.CompanionTheory.WhitLin.inner_eq_zero μ hN hx₀ h ?_
      rw [mem_valBall_iff_le_ord (mul_ne_zero h.ne_zero hx₀0), ord_mul h.ne_zero hx₀0]
      omega
  have hI : StronglyMeasurable I := by
    refine StronglyMeasurable.integral_prod_right (f := fun (h : Fˣ) (x : F) =>
      Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ)) ?_
    refine Continuous.stronglyMeasurable ?_
    exact (hΦ.1.continuous.comp GlobalTheory.CompanionTheory.WhitLin.continuous_line).mul
      ((GlobalTheory.CompanionTheory.WhitLin.continuous_circle hψ).comp continuous_snd)
  have hq : (1 : ℝ) ≤ residueCard F := by exact_mod_cast one_lt_residueCard.le
  set q : ℝ := (residueCard F : ℝ) with hqdef
  set Q : ℝ := max (q ^ (-M)) (q ^ B) with hQ
  set V : ℝ := C * μ.real (valBall F (M - B)) with hV
  have hmp1 : ∀ h : Fˣ, mp h 1 = ((modulus (h : F) : ℝ) : ℂ) := fun h => by simp [mp]
  have hcont : ∀ n, Continuous fun h : Fˣ => ((ν' n h : ℂˣ) : ℂ) := by
    intro n
    simp only [hν']
    exact (Units.continuous_val.comp hν.1).mul (continuous_mp _)
  have hval : ∀ a : Fˣ, Filter.Tendsto (fun n => ((ν' n a : ℂˣ) : ℂ)) Filter.atTop
      (nhds ((ν a : ℂˣ) : ℂ)) := by
    intro a
    simp only [hν']
    simpa using (tendsto_mp a hδ).const_mul ((ν a : ℂˣ) : ℂ)
  refine tendsto_integral_filter_of_dominated_convergence (S.indicator fun _ => Q * Q * (q ^ (-M) * V))
    ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun n => ?_
    have hc1 : Continuous fun h : Fˣ => (((ν' n h)⁻¹ * (ν' n)⁻¹ h : ℂˣ) : ℂ) := by
      simp only [MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
      have := (hcont n).inv₀ fun h => Units.ne_zero _
      exact this.mul this
    exact ((hc1.mul (continuous_mp 1)).stronglyMeasurable.mul hI).aestronglyMeasurable
  · have hev : ∀ᶠ n in Filter.atTop, |δ n| ≤ 1 := by
      have h0 : Filter.Tendsto (fun n => |δ n|) Filter.atTop (nhds 0) := by simpa using hδ.abs
      exact h0.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hev] with n hn
    refine Filter.Eventually.of_forall fun h => ?_
    by_cases hh : h ∈ S
    · rw [Set.indicator_of_mem hh]
      obtain ⟨hl, hu⟩ := (hmem h).1 hh
      have hm0 : (0 : ℝ) < (modulus (h : F) : ℝ) := by exact_mod_cast modulus_pos h.ne_zero
      have hmod : (modulus (h : F) : ℝ) = q ^ (-ord (h : F)) := by
        rw [modulus_of_ne_zero h.ne_zero]; push_cast; rfl
      have hm1 : (modulus (h : F) : ℝ) ≤ Q :=
        le_max_of_le_left (by rw [hmod]; exact zpow_le_zpow_right₀ hq (by omega))
      have hm2 : (modulus (h : F) : ℝ)⁻¹ ≤ Q :=
        le_max_of_le_right (by
          rw [hmod, ← _root_.zpow_neg, neg_neg]; exact zpow_le_zpow_right₀ hq (by omega))
      have hnv : ‖((ν' n h : ℂˣ) : ℂ)‖ = (modulus (h : F) : ℝ) ^ δ n := by
        rw [hν', norm_mul, hν.2, one_mul, GlobalTheory.CompanionTheory.DampedWhittakerGauge.norm_mp]
      have hb := inv_rpow_le hm0 hm1 hm2 hn
      have n1 : ‖(((ν' n h)⁻¹ * (ν' n)⁻¹ h : ℂˣ) : ℂ)‖ ≤ Q * Q := by
        simp only [MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
          norm_inv, hnv]
        exact mul_le_mul hb hb (by positivity) ((by positivity : (0 : ℝ) ≤ _).trans hb)
      have n2 : ‖mp h 1‖ ≤ q ^ (-M) := by
        rw [hmp1, Complex.norm_real, Real.norm_of_nonneg hm0.le, hmod]
        exact zpow_le_zpow_right₀ hq (by omega)
      have n3 : ‖I h‖ ≤ V := GlobalTheory.CompanionTheory.WhitLin.norm_inner_le μ hM hC h hu
      have hq0 : (0 : ℝ) ≤ q ^ (-M) := by positivity
      rw [norm_mul, norm_mul]
      calc _ ≤ Q * Q * q ^ (-M) * V := by gcongr
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hh]
      show ‖_ * I h‖ ≤ 0
      simp [hzero h hh]
  · exact (integrable_indicator_iff hSm).2 (integrableOn_const hSf)
  · refine Filter.Eventually.of_forall fun h => ?_
    simp only [MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    have hi := (hval h).inv₀ (Units.ne_zero _)
    exact ((hi.mul hi).mul_const _).mul_const _

end GlobalTheory.CompanionTheory.DampedWhittakerLimit

theorem GlobalTheory.CompanionTheory.DampedWhittakerLimit.damped_whittaker_tendsto : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ →
    ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ (ν' : ℕ → Fˣ →* ℂˣ) (δ : ℕ → ℝ),
    (∀ n a, ((ν' n a : ℂˣ) : ℂ) = ((ν a : ℂˣ) : ℂ) * mp a (δ n)) → Filter.Tendsto δ Filter.atTop (nhds 0) →
    ∀ φ₀ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ g : GL (Fin 2) F,
      Filter.Tendsto (fun n => W2 ψ (ν' n) (ν' n)⁻¹ φ₀ g) Filter.atTop (nhds (W2 ψ ν ν⁻¹ φ₀ g)) := by
  intro F _ _ _ _ _ _ ψ hψ ν hν ν' δ hν' hδ φ₀ hφ₀ g
  obtain ⟨hc, h1, -⟩ := hψ
  have hout := GlobalTheory.CompanionTheory.DampedWhittakerLimit.tendsto_outer (GlobalTheory.CompanionTheory.WhitLin.rt_mem hφ₀ g) hc h1
    (selfDualMeasure ψ) hν hν' hδ
  have hpre : Filter.Tendsto (fun n => (((ν' n)⁻¹ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      mp (GeneralLinearGroup.det g) (1 / 2)) Filter.atTop
      (nhds (((ν⁻¹ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (1 / 2))) := by
    refine Filter.Tendsto.mul_const _ ?_
    simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hν']
    have h2 := (GlobalTheory.CompanionTheory.DampedWhittakerLimit.tendsto_mp (GeneralLinearGroup.det g) hδ).const_mul
      ((ν (GeneralLinearGroup.det g) : ℂˣ) : ℂ)
    rw [mul_one] at h2
    exact h2.inv₀ (Units.ne_zero _)
  exact hpre.mul hout
