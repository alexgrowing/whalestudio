import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped ENNReal in
private theorem sq_on_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {S : Set G} (hS : MeasurableSet S) (N : ℕ) (hN : ∀ x : G, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) :
    eLpNorm (GlobalTheory.AutomorphicL2Unitary.lift Γ F) 2 (μ.restrict S) ≤ N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
  have hmeasF : AEStronglyMeasurable (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) μ :=
    GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
  have key : ∫⁻ x, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S) ≤
      (N : ℝ≥0∞) * ∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
    rw [← lintegral_indicator hS, GlobalTheory.AutomorphicL2Unitary.lintegral_eq_lintegral_tsum (Γ := Γ) ((hmeasF.enorm.pow_const _).indicator hS),
      ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
    refine lintegral_mono (fun q => ?_)
    have hq : ∀ γ : Γ, S.indicator (fun x => ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ))
        ((γ : G) * Quotient.out q) = {γ : Γ | (γ : G) * Quotient.out q ∈ S}.indicator
          (fun _ => ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ)) γ := by
      intro γ
      have hl : GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) ((γ : G) * Quotient.out q) =
          (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q := by
        rw [GlobalTheory.AutomorphicL2Unitary.lift, GlobalTheory.AutomorphicL2Unitary.mk_mul]
        exact congrArg _ (Quotient.out_eq q)
      by_cases h : (γ : G) * Quotient.out q ∈ S
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show γ ∈ {γ : Γ | (γ : G) * Quotient.out q ∈ S} from h), hl]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show γ ∉ {γ : Γ | (γ : G) * Quotient.out q ∈ S} from h)]
    rw [tsum_congr hq, ← tsum_subtype, ENNReal.tsum_set_const]
    gcongr
    have h1 := ENat.toENNReal_le.mpr (hN (Quotient.out q))
    simpa using h1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have hN2 : (N : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      simp
    · calc (N : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (N : ℝ≥0∞) ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast h0) (by norm_num)
        _ = N := ENNReal.rpow_one _
  calc (∫⁻ x, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S)) ^ (1 / 2 : ℝ)
      ≤ ((N : ℝ≥0∞) * ∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow key (by norm_num)
    _ = (N : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ _ := by gcongr

theorem UpperTheory.V.Cj.H.cvCount :
    UpperTheory.V.Cj.H.CvCount := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψc
  obtain ⟨C0, hC0⟩ := hψ.bounded_above_of_compact_support hψc
  have hC : ∀ z, ‖ψ z‖ ≤ max C0 0 := fun z => (hC0 z).trans (le_max_left _ _)
  have hC' : 0 ≤ max C0 0 := le_max_right _ _
  have hMfin : μ (tsupport ψ)⁻¹ ≠ ⊤ := (hψc.isCompact.inv).measure_lt_top.ne
  refine ⟨max C0 0 * (μ (tsupport ψ)⁻¹).toReal ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro x N hN F
  have hS : MeasurableSet {y : G | ψ (y⁻¹ * x) ≠ 0} :=
    (isOpen_ne_fun (hψ.comp (continuous_inv.mul continuous_const)) continuous_const).measurableSet
  have hSK : μ {y : G | ψ (y⁻¹ * x) ≠ 0} ≤ μ (tsupport ψ)⁻¹ := by
    calc μ {y : G | ψ (y⁻¹ * x) ≠ 0} ≤ μ ((fun y => x⁻¹ * y) ⁻¹' (tsupport ψ)⁻¹) := by
          refine measure_mono (fun y hy => ?_)
          show (x⁻¹ * y)⁻¹ ∈ tsupport ψ
          rw [_root_.mul_inv_rev, inv_inv]
          exact subset_tsupport _ hy
      _ = μ (tsupport ψ)⁻¹ := measure_preimage_mul μ x⁻¹ _
  have hF := sq_on_le Γ μ hS N hN F
  have hmeas : AEStronglyMeasurable (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) μ :=
    GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num)
    (hmeas.restrict (s := {y : G | ψ (y⁻¹ * x) ≠ 0}))
  rw [show (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) = (1 / 2 : ℝ) by norm_num,
    Measure.restrict_apply_univ] at hH
  have hE : ‖cv ψ F x‖ₑ ≤ (N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ)) *
      ENNReal.ofReal (max C0 0) := by
    calc ‖cv ψ F x‖ₑ ≤ ∫⁻ y, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y * ψ (y⁻¹ * x)‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y, {y : G | ψ (y⁻¹ * x) ≠ 0}.indicator
            (fun y => ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y‖ₑ) y * ENNReal.ofReal (max C0 0) ∂μ := by
          refine lintegral_mono (fun y => ?_)
          by_cases hy : y ∈ {y : G | ψ (y⁻¹ * x) ≠ 0}
          · rw [Set.indicator_of_mem hy, enorm_mul]
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hC _)
          · have h0 : ψ (y⁻¹ * x) = 0 := not_not.mp hy
            rw [h0, mul_zero, enorm_zero]
            exact bot_le
      _ = (∫⁻ y in {y : G | ψ (y⁻¹ * x) ≠ 0}, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y‖ₑ ∂μ) *
            ENNReal.ofReal (max C0 0) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hS]
      _ = eLpNorm (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) 1 (μ.restrict {y : G | ψ (y⁻¹ * x) ≠ 0}) *
            ENNReal.ofReal (max C0 0) := by
          rw [eLpNorm_one_eq_lintegral_enorm]
      _ ≤ _ := by
          gcongr
          calc _ ≤ _ := hH
            _ ≤ _ := by gcongr
  have hRfin : (N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ)) *
      ENNReal.ofReal (max C0 0) ≠ ⊤ := by
    have h1 : eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ≠ ⊤ := Lp.eLpNorm_ne_top F
    have h2 : μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hMfin
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) h1) h2)
      ENNReal.ofReal_ne_top
  calc ‖cv ψ F x‖ = ‖cv ψ F x‖ₑ.toReal := (toReal_enorm _).symm
    _ ≤ _ := ENNReal.toReal_mono hRfin hE
    _ = max C0 0 * (μ (tsupport ψ)⁻¹).toReal ^ (1 / 2 : ℝ) * N * ‖F‖ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC',
        ENNReal.toReal_rpow, ENNReal.toReal_natCast, Lp.norm_def]
      ring
