import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOnStatement

noncomputable section
open NumberField Topology MeasureTheory Filter Metric
open scoped Pointwise

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem countable_ratN (r : ℕ) : Countable (ratN E a r) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  refine Function.Surjective.countable (f := fun q : BlockIx a r → E =>
    (⟨fun p => algebraMap E (Ad E) (q p), q, rfl⟩ : ratN E a r)) ?_
  rintro ⟨x, q, rfl⟩
  exact ⟨q, rfl⟩

theorem covol_lt_top {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx a r → Ad E))
    (h : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) : μ 𝓕 < ⊤ := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have := countable_ratN (E := E) (a := a) r
  let Cm : Set (BlockIx a r → Ad E) := Set.univ.pi fun _ => K
  have hCm : IsCompact Cm := isCompact_univ_pi fun _ => hK
  have hcovm : ∀ x : BlockIx a r → Ad E, ∃ γ : ratN E a r, x ∈ γ +ᵥ Cm := by
    intro x
    choose q hq using fun p => hcov (x p)
    refine ⟨⟨fun p => algebraMap E (Ad E) (q p), q, rfl⟩, fun p => x p - algebraMap E (Ad E) (q p),
      fun p _ => hq p, ?_⟩
    funext p
    show algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p)) = x p
    abel
  have h1 : μ 𝓕 ≤ ∑' γ : ratN E a r, μ ((γ +ᵥ Cm) ∩ 𝓕) := by
    calc μ 𝓕 ≤ μ (⋃ γ : ratN E a r, ((γ +ᵥ Cm) ∩ 𝓕)) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨γ, hγ⟩ := hcovm x
          exact Set.mem_iUnion.mpr ⟨γ, hγ, hx⟩
      _ ≤ ∑' γ : ratN E a r, μ ((γ +ᵥ Cm) ∩ 𝓕) := measure_iUnion_le _
  have : MeasurableConstVAdd (ratN E a r) (BlockIx a r → Ad E) :=
    ⟨fun γ => (continuous_const.add continuous_id :
      Continuous fun x : BlockIx a r → Ad E => (γ : BlockIx a r → Ad E) + x).measurable⟩
  have : VAddInvariantMeasure (ratN E a r) (BlockIx a r → Ad E) μ :=
    ⟨fun γ s _ => measure_preimage_add μ (γ : BlockIx a r → Ad E) s⟩
  rw [← h.measure_eq_tsum Cm] at h1
  exact h1.trans_lt hCm.measure_lt_top

theorem chart_unip_periodic {r : ℕ} {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) (q : BlockIx a r → E)
    (x : BlockIx a r → Ad E) :
    chart φ.1 (unip ((fun p => algebraMap E (Ad E) (q p)) + x) * g) = chart φ.1 (unip x * g) := by
  rw [unip_add, unip_algebraMap, mul_assoc]
  funext y
  unfold chart
  split_ifs
  · rw [mul_assoc, hφ.left]
  · rfl

theorem chart_cont_bound {r : ℕ} {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) (X : Lie E a) :
    (∀ y ∈ invSet E a, Continuous fun x : BlockIx a r → Ad E => chart φ.1 (unip x * g) y) ∧
    (∀ y ∈ invSet E a, Continuous fun x : BlockIx a r → Ad E => fderiv ℝ (chart φ.1 (unip x * g)) y X) ∧
    ∀ S : Set (Lie E a), IsCompact S → S ⊆ invSet E a → ∃ C, ∀ x : BlockIx a r → Ad E, ∀ y ∈ S,
      ‖chart φ.1 (unip x * g) y‖ ≤ C ∧ ‖fderiv ℝ (chart φ.1 (unip x * g)) y X‖ ≤ C := by
  have h1 := (GlobalTheory.T.chart_unipotent_fderiv_continuousOn E a r φ hφ g X).1
  have h2 := (GlobalTheory.T.chart_unipotent_fderiv_continuousOn E a r φ hφ g X).2
  have hm : ∀ y ∈ invSet E a, ∀ x : BlockIx a r → Ad E,
      ((x, y) : (BlockIx a r → Ad E) × Lie E a) ∈ Set.univ ×ˢ invSet E a :=
    fun y hy x => Set.mem_prod.2 ⟨Set.mem_univ _, hy⟩
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun S hS hSi => ?_⟩
  · have := h1.comp_continuous (continuous_id.prodMk continuous_const) (hm y hy)
    exact this
  · have := h2.comp_continuous (continuous_id.prodMk continuous_const) (hm y hy)
    exact this
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hKc : IsCompact ((Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S) := (isCompact_univ_pi fun _ => hK).prod hS
  have hsub : (Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S ⊆ Set.univ ×ˢ invSet E a :=
    Set.prod_mono (Set.subset_univ _) hSi
  obtain ⟨C1, hC1⟩ := hKc.exists_bound_of_continuousOn (h1.mono hsub)
  obtain ⟨C2, hC2⟩ := hKc.exists_bound_of_continuousOn (h2.mono hsub)
  refine ⟨max C1 C2, fun x y hy => ?_⟩
  choose q hq using fun p => hcov (x p)
  have hx : x = (fun p => algebraMap E (Ad E) (q p)) + fun p => x p - algebraMap E (Ad E) (q p) := by
    funext p
    show x p = algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p))
    exact (add_sub_cancel _ _).symm
  have hx' : ((fun p => x p - algebraMap E (Ad E) (q p)), y) ∈ (Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S :=
    ⟨fun p _ => hq p, hy⟩
  rw [hx, chart_unip_periodic hφ]
  exact ⟨(hC1 _ hx').trans (le_max_left _ _), (hC2 _ hx').trans (le_max_right _ _)⟩

theorem isCuspidal_lie (X : Lie E a) (φ : Sm E a) (hφ : IsCuspForm φ) : IsCuspidal (lie E a X φ).1 := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  haveI := hμ
  obtain ⟨hc1, hc2, hb⟩ := chart_cont_bound (r := r) hφ.1 g X
  let ℓ : ℝ → Lie E a := fun t => oneL E a + t • X
  have hℓc : Continuous ℓ := continuous_const.add (continuous_id.smul continuous_const)
  have hT : IsOpen (ℓ ⁻¹' invSet E a) := isOpen_invSet.preimage hℓc
  have h0T : (0:ℝ) ∈ ℓ ⁻¹' invSet E a := by
    show oneL E a + (0:ℝ) • X ∈ invSet E a
    rw [zero_smul, add_zero]; exact isUnit_one
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hT 0 h0T
  have hε : 0 < δ / 2 := by positivity
  have hS : IsCompact (ℓ '' closedBall 0 (δ / 2)) := (isCompact_closedBall 0 (δ / 2)).image hℓc
  have hSinv : ℓ '' closedBall 0 (δ / 2) ⊆ invSet E a := by
    rintro _ ⟨t, ht, rfl⟩; exact hball (closedBall_subset_ball (by linarith) ht)
  obtain ⟨C, hC⟩ := hb _ hS hSinv
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hballT : ∀ t ∈ ball (0:ℝ) (δ / 2), ℓ t ∈ invSet E a := fun t ht => hball (ball_subset_ball (by linarith) ht)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕)
    (F := fun t x => chart φ.1 (unip x * g) (ℓ t))
    (F' := fun t x => fderiv ℝ (chart φ.1 (unip x * g)) (ℓ t) X) (x₀ := 0)
    (bound := fun _ => C) (s := ball 0 (δ / 2)) (ball_mem_nhds 0 hε) ?meas ?int ?meas' ?bd (integrable_const C) ?diff
  case meas =>
    filter_upwards [ball_mem_nhds (0:ℝ) hε] with t ht
    exact (hc1 _ (hballT t ht)).aestronglyMeasurable
  case int =>
    refine Integrable.of_bound (hc1 _ (hballT 0 (mem_ball_self hε))).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun x => (hC x _ ⟨0, mem_closedBall_self hε.le, rfl⟩).1
  case meas' => exact (hc2 _ (hballT 0 (mem_ball_self hε))).aestronglyMeasurable
  case bd =>
    exact Filter.Eventually.of_forall fun x t ht => (hC x _ ⟨t, ball_subset_closedBall ht, rfl⟩).2
  case diff =>
    refine Filter.Eventually.of_forall fun x t ht => ?_
    have hd := ((contDiffAt_chart φ.2 (unip x * g) (hballT t ht)).differentiableAt (by simp)).hasFDerivAt
    have hl : HasDerivAt ℓ X t := by
      have := ((hasDerivAt_id t).smul_const X).const_add (oneL E a)
      rw [one_smul] at this
      exact this
    exact hd.comp_hasDerivAt t hl
  have heq : (fun t => ∫ x in 𝓕, chart φ.1 (unip x * g) (ℓ t) ∂μ) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [ball_mem_nhds (0:ℝ) hε] with t ht
    have hu : IsUnit (Matrix.of (ℓ t)) := hballT t ht
    have e : ∀ x : BlockIx a r → Ad E, chart φ.1 (unip x * g) (ℓ t) = φ.1 (unip x * (g * infGL E a hu.unit)) := fun x => by
      rw [chart, dif_pos hu, mul_assoc]
    simp only [e]
    exact hφ.2 r h0 h1 μ 𝓕 hμ hF _
  have h2 := key.2.unique ((hasDerivAt_const (0:ℝ) (0:ℂ)).congr_of_eventuallyEq heq)
  have e0 : ℓ 0 = oneL E a := by simp [ℓ]
  simp only [e0] at h2
  exact h2

theorem isCuspidal_lie_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (X : Lie E a) (φ : Sm E a), IsCuspForm φ → IsCuspidal (lie E a X φ).1 :=
  fun _ _ _ _ _ X φ h => isCuspidal_lie X φ h

end GlobalTheory.CuspRep
