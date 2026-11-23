import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2Statement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocalUnitaryL2

open Filter
open scoped ENNReal NNReal

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

local instance mA : MeasurableSpace (κ → AF F) := borel _
local instance bA : BorelSpace (κ → AF F) := ⟨rfl⟩
local instance mV (v : Pl F) : MeasurableSpace (κ → Fv F v) := borel _
local instance bV (v : Pl F) : BorelSpace (κ → Fv F v) := ⟨rfl⟩

theorem continuous_evFin (v : Pl F) : Continuous (evFin F v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

def prj (v : Pl F) (x : κ → AF F) : κ → Fv F v := fun i => evFin F v (x i)

theorem continuous_prj (v : Pl F) : Continuous (prj (κ := κ) v) :=
  continuous_pi fun i => (continuous_evFin v).comp (continuous_apply i)

def lift (v : Pl F) (y : κ → Fv F v) : κ → AF F := fun i => GlobalTheory.EmbChart.atPlace v (y i)

theorem at_lift (v : Pl F) (y : κ → Fv F v) : At (evFin F v) (lift v y) := by
  intro u hu
  funext i
  show u * GlobalTheory.EmbChart.atPlace v (y i) = 0
  rw [mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]

theorem prj_add_lift (v : Pl F) (x : κ → AF F) (y : κ → Fv F v) : prj v (x + lift v y) = prj v x + y := by
  funext i
  simp [prj, lift, map_add, GlobalTheory.EmbChart.evFin_atPlace]

def box (v : Pl F) (y₀ : κ → Fv F v) : Set (κ → Fv F v) := {y | ∀ k, y k - y₀ k ∈ v.adicCompletionIntegers F}

theorem sb_box (v : Pl F) (y₀ : κ → Fv F v) : (box v y₀).indicator (1 : (κ → Fv F v) → ℂ) ∈ SB (κ → Fv F v) := by
  have h := GlobalTheory.StdVacuum.indicator_mem_SB (κ := κ) v
  have e : (box v y₀).indicator (1 : (κ → Fv F v) → ℂ) =
      ({x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F}.indicator 1) ∘ (Homeomorph.subRight y₀) := by
    funext y
    by_cases hy : y ∈ box v y₀
    · have hm : (Homeomorph.subRight y₀) y ∈ {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} :=
        fun k => by simpa using hy k
      rw [Set.indicator_of_mem hy, Function.comp_apply, Set.indicator_of_mem hm]; rfl
    · have hm : (Homeomorph.subRight y₀) y ∉ {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} :=
        fun h' => hy fun k => by simpa using h' k
      rw [Set.indicator_of_notMem hy, Function.comp_apply, Set.indicator_of_notMem hm]
  rw [e]
  exact ⟨h.1.comp_continuous (Homeomorph.subRight y₀).continuous, h.2.comp_homeomorph _⟩

theorem mem_box_self (v : Pl F) (y₀ : κ → Fv F v) : y₀ ∈ box v y₀ := fun k => by simp

theorem box_eq_fiber (v : Pl F) (y₀ : κ → Fv F v) :
    box v y₀ = (box v y₀).indicator (1 : (κ → Fv F v) → ℂ) ⁻¹' {1} := by
  ext y
  by_cases hy : y ∈ box v y₀ <;> simp [hy]

theorem isOpen_box (v : Pl F) (y₀ : κ → Fv F v) : IsOpen (box v y₀) := by
  rw [box_eq_fiber]; exact (sb_box v y₀).1.isOpen_fiber 1

theorem isCompact_closure_box (v : Pl F) (y₀ : κ → Fv F v) : IsCompact (closure (box v y₀)) := by
  have h := (sb_box v y₀).2
  unfold HasCompactSupport tsupport at h
  rwa [Set.support_indicator, Function.support_one, Set.inter_univ] at h

end GlobalTheory.LocalUnitaryL2

namespace GlobalTheory.LocalUnitaryL2

open Filter
open scoped ENNReal NNReal

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

local instance mA' : MeasurableSpace (κ → AF F) := borel _
local instance bA' : BorelSpace (κ → AF F) := ⟨rfl⟩
local instance mV' (v : Pl F) : MeasurableSpace (κ → Fv F v) := borel _
local instance bV' (v : Pl F) : BorelSpace (κ → Fv F v) := ⟨rfl⟩

section Meas

variable (v : Pl F) (r : (κ → AF F) → ℂ)
  (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x)
  (hS : ∀ ψ ∈ SB (κ → Fv F v), tens (evFin F v) ψ r ∈ schA F κ)

include hS in
theorem continuous_r : Continuous r := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hc := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hS _ (sb_box v (prj v x₀)))
  refine hc.continuousAt.congr ?_
  filter_upwards [(continuous_prj v).continuousAt.preimage_mem_nhds
    ((isOpen_box v (prj v x₀)).mem_nhds (mem_box_self v _))] with x hx
  show (box v (prj v x₀)).indicator (1 : (κ → Fv F v) → ℂ) (fun i => evFin F v (x i)) * r x = r x
  rw [Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ box v (prj v x₀) from hx), Pi.one_apply, one_mul]

def nu (μA : Measure (κ → AF F)) : Measure (κ → Fv F v) :=
  (μA.withDensity fun x => ‖r x‖ₑ ^ 2).map (prj v)

include hS in
theorem lintegral_nu (μA : Measure (κ → AF F)) {g : (κ → Fv F v) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂nu v r μA = ∫⁻ x, ‖r x‖ₑ ^ 2 * g (prj v x) ∂μA := by
  have hd : Measurable fun x => ‖r x‖ₑ ^ 2 := ((continuous_r v r hS).measurable.enorm).pow_const 2
  rw [nu, lintegral_map hg (continuous_prj v).measurable]
  exact lintegral_withDensity_eq_lintegral_mul μA hd (hg.comp (continuous_prj v).measurable)

include hS in
theorem lintegral_nu_sq (μA : Measure (κ → AF F)) {ψ : (κ → Fv F v) → ℂ} (hψ : Continuous ψ) :
    ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂nu v r μA = ∫⁻ x, ‖tens (evFin F v) ψ r x‖ₑ ^ 2 ∂μA := by
  rw [lintegral_nu v r hS μA ((hψ.measurable.enorm).pow_const 2)]
  congr 1; funext x
  show _ = ‖ψ (prj v x) * r x‖ₑ ^ 2
  rw [enorm_mul, mul_pow, mul_comm]

include hr hS in
theorem nu_invariant (μA : Measure (κ → AF F)) [μA.IsAddHaarMeasure] : (nu v r μA).IsAddLeftInvariant := by
  refine ⟨fun y => Measure.ext fun s hs => ?_⟩
  have hs' : MeasurableSet ((fun z => y + z) ⁻¹' s) := measurable_const_add y hs
  rw [Measure.map_apply (measurable_const_add y) hs, ← lintegral_indicator_one hs,
    ← lintegral_indicator_one hs', lintegral_nu v r hS μA (measurable_one.indicator hs),
    lintegral_nu v r hS μA (measurable_one.indicator hs')]
  conv_rhs => rw [← lintegral_add_left_eq_self _ (lift v y)]
  congr 1; funext x
  rw [add_comm (lift v y) x, hr x _ (at_lift v y), prj_add_lift]
  by_cases hx : y + prj v x ∈ s
  · rw [Set.indicator_of_mem (show prj v x ∈ (fun z => y + z) ⁻¹' s from hx), Set.indicator_of_mem
      (show prj v x + y ∈ s by rwa [add_comm])]; rfl
  · rw [Set.indicator_of_notMem (show prj v x ∉ (fun z => y + z) ⁻¹' s from hx), Set.indicator_of_notMem
      (show prj v x + y ∉ s by rwa [add_comm])]

theorem nu_box_eq (μA : Measure (κ → AF F)) (y₀ : κ → Fv F v) :
    nu v r μA (box v y₀) = ∫⁻ y, ‖(box v y₀).indicator (1 : (κ → Fv F v) → ℂ) y‖ₑ ^ 2 ∂nu v r μA := by
  rw [← lintegral_indicator_one (isOpen_box v y₀).measurableSet]
  congr 1; funext y
  by_cases hy : y ∈ box v y₀ <;> simp [hy]

include hS in
theorem nu_box_lt_top (μA : Measure (κ → AF F)) [μA.IsAddHaarMeasure] (y₀ : κ → Fv F v) :
    nu v r μA (box v y₀) < ⊤ := by
  rw [nu_box_eq, lintegral_nu_sq v r hS μA (sb_box v y₀).1.continuous]
  have hL := GlobalTheory.T.adelic_schwartz_mem_L2 F κ μA inferInstance _ (hS _ (sb_box v y₀))
  have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hL.eLpNorm_lt_top
  simpa using this

include hS in
theorem nu_locFin (μA : Measure (κ → AF F)) [μA.IsAddHaarMeasure] : IsLocallyFiniteMeasure (nu v r μA) :=
  ⟨fun y => ⟨box v y, (isOpen_box v y).mem_nhds (mem_box_self v y), nu_box_lt_top v r hS μA y⟩⟩

include hS in
theorem nu_box_ne_zero (μA : Measure (κ → AF F)) [μA.IsAddHaarMeasure] {x₀ : κ → AF F} (h0 : r x₀ ≠ 0) :
    nu v r μA (box v (prj v x₀)) ≠ 0 := by
  rw [nu_box_eq, lintegral_nu_sq v r hS μA (sb_box v _).1.continuous]
  intro hz
  have hc := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hS _ (sb_box v (prj v x₀)))
  have hcm : Continuous fun x => ‖tens (evFin F v) ((box v (prj v x₀)).indicator (1 : (κ → Fv F v) → ℂ)) r x‖ₑ ^ 2 :=
    (ENNReal.continuous_pow 2).comp hc.enorm
  rw [lintegral_eq_zero_iff hcm.measurable] at hz
  have h1 := congrFun ((Continuous.ae_eq_iff_eq μA hcm continuous_const).1 hz) x₀
  have h2 : tens (evFin F v) ((box v (prj v x₀)).indicator (1 : (κ → Fv F v) → ℂ)) r x₀ = r x₀ := by
    show (box v (prj v x₀)).indicator (1 : (κ → Fv F v) → ℂ) (prj v x₀) * r x₀ = r x₀
    rw [Set.indicator_of_mem (mem_box_self v _), Pi.one_apply, one_mul]
  rw [h2] at h1
  simp at h1
  exact h0 h1

include hr hS in
theorem exists_const (μA : Measure (κ → AF F)) [μA.IsAddHaarMeasure] (h0 : ∃ x₀, r x₀ ≠ 0)
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ ψ ∈ SB (κ → Fv F v),
      ∫⁻ x, ‖tens (evFin F v) ψ r x‖ₑ ^ 2 ∂μA = c * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
  haveI := nu_invariant v r hr hS μA
  haveI := nu_locFin v r hS μA
  obtain ⟨x₀, hx₀⟩ := h0
  set c := Measure.addHaarScalarFactor (nu v r μA) μ
  have key : ∀ s : Set (κ → Fv F v), IsCompact (closure s) → nu v r μA s = (c : ℝ≥0∞) * μ s := fun s hs => by
    rw [Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure _ μ hs]; rfl
  refine ⟨c, ?_, ENNReal.coe_ne_top, fun ψ hψ => ?_⟩
  · intro hc
    apply nu_box_ne_zero v r hS μA hx₀
    rw [key _ (isCompact_closure_box v _), hc, zero_mul]
  · rw [← lintegral_nu_sq v r hS μA hψ.1.continuous]
    have hK : IsCompact (tsupport ψ) := hψ.2
    have hres : (nu v r μA).restrict (tsupport ψ) = (c : ℝ≥0∞) • μ.restrict (tsupport ψ) := by
      ext s hs
      rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
      exact key _ (hK.of_isClosed_subset isClosed_closure
        (closure_minimal Set.inter_subset_right (isClosed_tsupport ψ)))
    have hsupp : Function.support (fun y => ‖ψ y‖ₑ ^ 2) ⊆ tsupport ψ := by
      intro y hy; apply subset_tsupport; intro h; apply hy; simp [h]
    rw [← setLIntegral_eq_of_support_subset hsupp, ← setLIntegral_eq_of_support_subset (μ := μ) hsupp, hres,
      lintegral_smul_measure, smul_eq_mul]

end Meas

end GlobalTheory.LocalUnitaryL2

namespace GlobalTheory.LocalUnitaryL2

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

open scoped Classical in

theorem exists_r (v : Pl F) : ∃ r : (κ → AF F) → ℂ, (∀ x z, At (evFin F v) z → r (x + z) = r x) ∧
    (∀ ψ ∈ SB (κ → Fv F v), tens (evFin F v) ψ r ∈ schA F κ) ∧ r 0 ≠ 0 := by
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  let φs : ∀ w : Pl F, (κ → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  refine ⟨r, hr, fun ψ hψ => ?_, ?_⟩
  · rw [hrt ψ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v ψ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hψ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  · have e := congrFun (hrt (fun _ => 1)) 0
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at e
    rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have hI : (fun i : κ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
      funext i
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : AF F).1 = 0
      exact map_zero _
    have hP : (∏ᶠ w, Function.update φs v (fun _ => 1) w fun i => evFin F w ((0 : κ → AF F) i)) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun w => ?_
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]
      · rw [Function.update_of_ne hw]
        simp only [φs, Pi.zero_apply, map_zero]
        rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
        rfl
    rw [hI, hP, mul_one]
    exact hf

end GlobalTheory.LocalUnitaryL2

theorem GlobalTheory.LocalUnitaryL2.lintegral_eq : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl F, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
    ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ →
    ∀ μ : @Measure (Fin a × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT v h _ φ hφ φ₁ hφ₁ hA μ hμ
  letI : MeasurableSpace (Fin a × Fin (a + a') → AF F) := borel _
  haveI : BorelSpace (Fin a × Fin (a + a') → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (Fin a × Fin (a + a') → Fv F v) := borel _
  haveI : BorelSpace (Fin a × Fin (a + a') → Fv F v) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨r, hr, hS, h0⟩ := GlobalTheory.LocalUnitaryL2.exists_r (κ := Fin a × Fin (a + a')) v
  let μA : Measure (Fin a × Fin (a + a') → AF F) := Measure.addHaar
  obtain ⟨c, hc0, hct, hc⟩ := GlobalTheory.LocalUnitaryL2.exists_const v r hr hS μA ⟨0, h0⟩ μ
  have hU := hT.weil.1.1.unit μA inferInstance h (tens (evFin F v) φ r) (hS φ hφ)
  have hAct : om (1, h) (tens (evFin F v) φ r) = tens (evFin F v) φ₁ r := hA r ⟨hr, hS φ hφ⟩
  change ∫⁻ x, ‖om (1, h) (tens (evFin F v) φ r) x‖ₑ ^ 2 ∂μA = _ at hU
  rw [hAct, hc φ₁ hφ₁, hc φ hφ] at hU
  exact (ENNReal.mul_right_inj hc0 hct).1 hU
