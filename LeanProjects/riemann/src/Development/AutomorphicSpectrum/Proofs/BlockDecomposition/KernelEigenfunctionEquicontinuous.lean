import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantTotallyComplexStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.EnnrealRpowTwoEqSq
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral

open scoped Pointwise

theorem sq_lintegral_mul_le {X : Type*} [MeasurableSpace X] (ν : Measure X) {a b : X → ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) :
    (∫⁻ w, a w * b w ∂ν) ^ 2 ≤ (∫⁻ w, a w ∂ν) * ∫⁻ w, a w * b w ^ 2 ∂ν :=
  _root_.UpperTheory.Reformulated.B.P6.r96a.GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral.sq_lintegral_mul_le ν ha hb

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem eventually_lintegral_translate_le [LocallyCompactSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {α : G → ℂ} (hα : Continuous α) (hs : HasCompactSupport α)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 (1 : G), ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≤ ε := by
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  have hC : IsCompact (V * tsupport α) := hVc.mul hs
  set C : Set G := V * tsupport α with hCdef
  have hfin : μ C ≠ ∞ := hC.measure_lt_top.ne
  have hc : 0 < ε / (μ C + 1) :=
    ENNReal.div_pos hε.ne' (by simp [hfin])
  set c : ℝ≥0∞ := ε / (μ C + 1) with hcdef
  have hunif : ∀ᶠ y in 𝓝 (1 : G), ∀ w ∈ C, ‖α (y⁻¹ * w) - α w‖ₑ < c := by
    refine hC.eventually_forall_of_forall_eventually fun w _ => ?_
    have hcont : Continuous fun z : G × G => ‖α (z.1⁻¹ * z.2) - α z.2‖ₑ := by
      fun_prop
    have h0 : ‖α ((1 : G)⁻¹ * w) - α w‖ₑ < c := by simpa using hc
    exact hcont.continuousAt.eventually_lt continuousAt_const h0
  filter_upwards [hunif, hV] with y hy hyV
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hle : ∀ w, ‖α (y⁻¹ * w) - α w‖ₑ ≤ C.indicator (fun _ => c) w := by
    intro w
    by_cases hw : w ∈ C
    · rw [Set.indicator_of_mem hw]
      exact (hy w hw).le
    · rw [Set.indicator_of_notMem hw]
      have h1 : α w = 0 := by
        by_contra h
        exact hw (Set.mem_mul.2 ⟨1, mem_of_mem_nhds hV, w, subset_tsupport _ h, one_mul w⟩)
      have h2 : α (y⁻¹ * w) = 0 := by
        by_contra h
        exact hw (Set.mem_mul.2 ⟨y, hyV, y⁻¹ * w, subset_tsupport _ h, by group⟩)
      simp [h1, h2]
  calc ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≤ ∫⁻ w, C.indicator (fun _ => c) w ∂μ := lintegral_mono hle
    _ = c * μ C := lintegral_indicator_const hCm c
    _ ≤ c * (μ C + 1) := by gcongr; exact le_self_add
    _ = ε := ENNReal.div_mul_cancel (by simp) (by simp [hfin])

variable [LocallyCompactSpace G] [SecondCountableTopology G]

theorem enorm_translate_sub_le (μ : Measure G) [μ.IsHaarMeasure] {α ψ : G → ℂ} (hα : Continuous α)
    (hs : HasCompactSupport α) (hψ : Continuous ψ) {s : ℂ}
    (hrep : ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) (x y : G) :
    ‖s‖ₑ * ‖ψ (x * y) - ψ x‖ₑ ≤ ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ * ‖ψ (x * w)‖ₑ ∂μ := by
  have h1 : s * ψ (x * y) = ∫ w, α (y⁻¹ * w) * ψ (x * w) ∂μ := by
    rw [← hrep (x * y), ← integral_mul_left_eq_self (fun w => α (y⁻¹ * w) * ψ (x * w)) y]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp [mul_assoc]
  have hcs : HasCompactSupport fun w => α (y⁻¹ * w) := hs.comp_homeomorph (Homeomorph.mulLeft y⁻¹)
  have hi1 : Integrable (fun w => α (y⁻¹ * w) * ψ (x * w)) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hcs.mul_right
  have hi2 : Integrable (fun w => α w * ψ (x * w)) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hs.mul_right
  have h3 : s * (ψ (x * y) - ψ x) = ∫ w, (α (y⁻¹ * w) - α w) * ψ (x * w) ∂μ := by
    rw [mul_sub, h1, ← hrep x, ← integral_sub hi1 hi2]
    exact integral_congr_ae (ae_of_all _ fun w => by ring)
  rw [← enorm_mul, h3]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  exact lintegral_congr fun w => enorm_mul _ _

theorem lintegral_right_translate (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {ψ : G → ℂ}
    (hl : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (w : G) :
    ∫⁻ x in F, ‖ψ (x * w)‖ₑ ^ 2 ∂μ = ∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ := by
  have hF' : IsFundamentalDomain Γ (MulOpposite.op w • F) μ := hF.smul_of_comm (MulOpposite.op w)
  have himg : (fun x => x * w) '' F = MulOpposite.op w • F := rfl
  have h1 := (measurePreserving_mul_right μ w).setLIntegral_comp_emb
    (MeasurableEquiv.mulRight w).measurableEmbedding (fun x => ‖ψ x‖ₑ ^ 2) F
  rw [h1, himg]
  refine hF'.setLIntegral_eq hF _ fun γ x => ?_
  simp only [Subgroup.smul_def, smul_eq_mul]
  rw [hl _ γ.2]

theorem sq_mean_translate_le (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {α ψ : G → ℂ}
    (hα : Continuous α) (hs : HasCompactSupport α) (hψ : Continuous ψ)
    (hl : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) {s : ℂ}
    (hrep : ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x)
    (hn : (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1) (y : G)
    (hA : ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≠ ∞) :
    ‖s‖ₑ ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ (∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ) ^ 2 := by
  set a : G → ℝ≥0∞ := fun w => ‖α (y⁻¹ * w) - α w‖ₑ with ha_def
  have hac : Continuous a := by fun_prop
  have ha : Measurable a := hac.measurable
  have hjm : Measurable fun z : G × G => a z.2 * ‖ψ (z.1 * z.2)‖ₑ ^ 2 := by
    have hc : Continuous fun z : G × G => ‖ψ (z.1 * z.2)‖ₑ := by fun_prop
    exact (ha.comp measurable_snd).mul (hc.measurable.pow_const 2)
  calc ‖s‖ₑ ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ
      = ∫⁻ x in F, (‖s‖ₑ * ‖ψ (x * y) - ψ x‖ₑ) ^ 2 ∂μ := by
        rw [← lintegral_const_mul' _ _ (by simp)]
        exact lintegral_congr fun x => (mul_pow _ _ _).symm
    _ ≤ ∫⁻ x in F, (∫⁻ w, a w * ‖ψ (x * w)‖ₑ ∂μ) ^ 2 ∂μ :=
        lintegral_mono fun x => by
          gcongr
          exact enorm_translate_sub_le μ hα hs hψ hrep x y
    _ ≤ ∫⁻ x in F, (∫⁻ w, a w ∂μ) * ∫⁻ w, a w * ‖ψ (x * w)‖ₑ ^ 2 ∂μ ∂μ :=
        lintegral_mono fun x => sq_lintegral_mul_le μ ha (by
          have : Continuous fun w => ‖ψ (x * w)‖ₑ := by fun_prop
          exact this.measurable)
    _ = (∫⁻ w, a w ∂μ) * ∫⁻ x in F, ∫⁻ w, a w * ‖ψ (x * w)‖ₑ ^ 2 ∂μ ∂μ :=
        lintegral_const_mul' _ _ hA
    _ = (∫⁻ w, a w ∂μ) * ∫⁻ w, ∫⁻ x in F, a w * ‖ψ (x * w)‖ₑ ^ 2 ∂μ ∂μ := by
        rw [lintegral_lintegral_swap hjm.aemeasurable]
    _ = (∫⁻ w, a w ∂μ) * ∫⁻ w, a w ∂μ := by
        congr 1
        refine lintegral_congr fun w => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_right_translate μ Γ hF hl w, hn, mul_one]
    _ = (∫⁻ w, a w ∂μ) ^ 2 := (sq _).symm

theorem exists_nhds_sq_mean_le (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] {α : G → ℂ} {δ : ℝ} {F : Set G}
    (hα : Continuous α) (hs : HasCompactSupport α) (hδ : 0 < δ) (hF : IsFundamentalDomain Γ F μ)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ U ∈ 𝓝 (1 : G), ∀ ψ : G → ℂ, Continuous ψ → (∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) →
      (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) →
      (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 → ∀ y ∈ U, ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  set d : ℝ≥0∞ := ENNReal.ofReal δ with hd
  have hd0 : d ≠ 0 := by simpa [hd] using hδ
  have hdt : d ≠ ∞ := ENNReal.ofReal_ne_top
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd0
  have hd2t : d ^ 2 ≠ ∞ := ENNReal.pow_ne_top hdt
  set ε : ℝ≥0∞ := min 1 (η * d ^ 2) with hε
  have hε0 : 0 < ε := lt_min one_pos (ENNReal.mul_pos hη.ne' hd2)
  have hε1 : ε ≤ 1 := min_le_left _ _
  refine ⟨_, eventually_lintegral_translate_le μ hα hs hε0, ?_⟩
  rintro ψ hψ hl ⟨s, hsδ, hrep⟩ hn y hy
  have hy' : ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≤ ε := hy
  have hA : ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≠ ∞ := (hy'.trans hε1).trans_lt ENNReal.one_lt_top |>.ne
  have hb := sq_mean_translate_le μ Γ hF hα hs hψ hl hrep hn y hA
  have hds : d ≤ ‖s‖ₑ := by
    rw [hd, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal hsδ
  have hεε : ε ^ 2 ≤ η * d ^ 2 := by
    calc ε ^ 2 = ε * ε := sq ε
      _ ≤ 1 * ε := by gcongr
      _ = ε := one_mul ε
      _ ≤ η * d ^ 2 := min_le_right _ _
  have hfin : d ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ d ^ 2 * η := by
    calc d ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ
        ≤ ‖s‖ₑ ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ := by gcongr
      _ ≤ (∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ) ^ 2 := hb
      _ ≤ ε ^ 2 := by gcongr
      _ ≤ η * d ^ 2 := hεε
      _ = d ^ 2 * η := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_right hd2 hd2t).1 hfin

end GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral

theorem GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∀ η : ℝ≥0∞, 0 < η → ∃ U ∈ 𝓝 (1 : GA E N), ∀ ψ : GA E N → ℂ, Continuous ψ →
  (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) → (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) →
  (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 → ∀ y ∈ U, ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  intro E _ _ _ N _ _ μ _ α δ F hα hs hδ hF η hη
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.haar_right_invariant_totally_complex E N μ
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  exact GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral.exists_nhds_sq_mean_le μ (latticeGL E N) hα hs hδ hF hη
