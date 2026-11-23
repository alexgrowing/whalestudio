import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr GlobalTheory.AdelicU MeasureTheory
open scoped Matrix ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.TensorSquareIntegral

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mulSupport_finite (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hφ : ∀ᶠ v in Filter.cofinite, φ v = GlobalTheory.RatWeilOp.ind κ v)
    (x : κ → AF F) : (Function.mulSupport fun v : Pl F => φ v (fun i => evFin F v (x i))).Finite := by
  have hev : ∀ᶠ v in Filter.cofinite, φ v = GlobalTheory.RatWeilOp.ind κ v ∧ ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
    hφ.and (Filter.eventually_all.2 fun i => (x i).2.2.mono fun _ hv => hv)
  refine (Filter.eventually_cofinite.1 hev).subset fun v hv hP => hv ?_
  show φ v _ = 1
  rw [hP.1]
  exact Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {z : κ → Fv F v | ∀ i, z i ∈ v.adicCompletionIntegers F}
    from hP.2) 1

theorem pure_mul_conj (f f' : SInf F κ) (φ φ' : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = GlobalTheory.RatWeilOp.ind κ v) (hφ' : ∀ᶠ v in Filter.cofinite, φ' v = GlobalTheory.RatWeilOp.ind κ v)
    (x : κ → AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * conj (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' x) = (f (fun i => evI F (x i)) * conj (f' (fun i => evI F (x i)))) *
      ∏ᶠ v, (φ v (fun i => evFin F v (x i)) * conj (φ' v (fun i => evFin F v (x i)))) := by
  have h1 := mulSupport_finite φ hφ x
  have h2 := mulSupport_finite φ' hφ' x
  have h3 : (Function.mulSupport fun v : Pl F => conj (φ' v (fun i => evFin F v (x i)))).Finite := by
    refine h2.subset fun v hv h => hv ?_
    simp only [Function.mem_mulSupport, ne_eq, not_not] at h ⊢
    rw [h, map_one]
  have hc : conj (∏ᶠ v, φ' v (fun i => evFin F v (x i))) = ∏ᶠ v, conj (φ' v (fun i => evFin F v (x i))) :=
    MonoidHom.map_finprod (starRingEnd ℂ).toMonoidHom h2
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, map_mul, hc, finprod_mul_distrib h1 h3]
  ring

theorem mul_conj_mem_SB {X : Type} [TopologicalSpace X] {φ φ' : X → ℂ} (hφ : φ ∈ SB X) (hφ' : φ' ∈ SB X) :
    (fun t => φ t * conj (φ' t)) ∈ SB X :=
  ⟨hφ.1.mul (hφ'.1.comp _), hφ.2.mul_right⟩

theorem ind_mul_conj (v : Pl F) : (fun t => GlobalTheory.RatWeilOp.ind κ v t * conj (GlobalTheory.RatWeilOp.ind κ v t)) = GlobalTheory.RatWeilOp.ind κ v := by
  funext t
  by_cases h : t ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
  · simp [GlobalTheory.RatWeilOp.ind, Set.indicator_of_mem h]
  · simp [GlobalTheory.RatWeilOp.ind, Set.indicator_of_notMem h]

end GlobalTheory.TensorSquareIntegral

noncomputable section

namespace GlobalTheory.TensorSquareIntegral

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem lintegral_sq_eq {X : Type} [MeasurableSpace X] {μ : Measure X} {g : X → ℂ}
    (hg : Integrable (fun x => g x * conj (g x)) μ) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, g x * conj (g x) ∂μ).re := by
  have e : ∀ x, g x * conj (g x) = ((‖g x‖ ^ 2 : ℝ) : ℂ) := fun x => by rw [Complex.mul_conj']; push_cast; rfl
  have hi : Integrable (fun x => ‖g x‖ ^ 2) μ := by
    refine hg.norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [e x, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_complex_ofReal, Complex.ofReal_re,
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem integrable_mul_conj [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure] (f f' : SInf F κ) :
    Integrable (fun z => f z * conj (f' z)) μi :=
  (f.integrable (μ := μi)).mul_bdd ((Complex.continuous_conj.comp f'.continuous).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => by
      rw [Complex.norm_conj]
      exact f'.norm_le_seminorm ℝ z)

theorem integral_ind (v : Pl F) [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (ν : Measure (κ → Fv F v))
    (h1 : ν {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1) :
    ∫ t, GlobalTheory.RatWeilOp.ind κ v t * conj (GlobalTheory.RatWeilOp.ind κ v t) ∂ν = 1 := by
  rw [ind_mul_conj]
  have hs : MeasurableSet {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
    have : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
        Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by ext x; simp
    rw [this]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).measurableSet
  show ∫ t, Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (fun _ => (1 : ℂ)) t ∂ν = 1
  rw [integral_indicator_const _ hs, Measure.real, h1]
  simp

theorem integral_pure_mul_conj [MeasurableSpace (κ → AF F)] [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)]
    [BorelSpace (κ → mixedEmbedding.mixedSpace F)] [∀ v : Pl F, MeasurableSpace (κ → Fv F v)]
    (μ : Measure (κ → AF F)) (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μv : ∀ v : Pl F, Measure (κ → Fv F v)) (c₀ : ℂ)
    (hpure : ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), Continuous f →
      Integrable f μi → GlobalTheory.RatWeilOp.IsFam φ →
        Integrable (fun x : κ → AF F => f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) μ ∧
        ∫ x, f (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ =
          c₀ * (∫ x, f x ∂μi) * ∏ᶠ v, ∫ x, φ v x ∂(μv v))
    (f f' : SInf F κ) (φ φ' : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hφ : GlobalTheory.RatWeilOp.IsFam φ) (hφ' : GlobalTheory.RatWeilOp.IsFam φ') :
    Integrable (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * conj (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' x)) μ ∧
    ∫ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * conj (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' x) ∂μ =
      c₀ * (∫ z, f z * conj (f' z) ∂μi) * ∏ᶠ v, ∫ t, φ v t * conj (φ' v t) ∂(μv v) := by
  have hfam : GlobalTheory.RatWeilOp.IsFam (fun v t => φ v t * conj (φ' v t)) := by
    refine ⟨fun v => mul_conj_mem_SB (hφ.1 v) (hφ'.1 v), ?_⟩
    filter_upwards [hφ.2, hφ'.2] with v h1 h2
    rw [h1, h2]
    exact ind_mul_conj v
  have hfc : Continuous (fun z => f z * conj (f' z)) := f.continuous.mul (Complex.continuous_conj.comp f'.continuous)
  obtain ⟨h1, h2⟩ := hpure _ _ hfc (integrable_mul_conj μi f f') hfam
  have e := funext (pure_mul_conj f f' φ φ' hφ.2 hφ'.2)
  beta_reduce at h1 h2
  rw [e]
  exact ⟨h1, h2⟩

end GlobalTheory.TensorSquareIntegral

noncomputable section

namespace GlobalTheory.TensorSquareIntegral

open scoped Classical

theorem exists_const_tensor : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (vac vac₁ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (ei : SInf F κ →L[ℂ] SInf F κ) (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, vac v ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (∀ᶠ v in Filter.cofinite, vac₁ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (∀ v, ev v (vac v) = vac₁ v) → (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ f φ, (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = vac v) →
      e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    (∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => ei f x * starRingEnd ℂ (ei f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x))) →
    (∀ v : Pl F, ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => ev v φ x * starRingEnd ℂ (ev v φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x))) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F κ, ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ e vac vac₁ ei ev hvSB hvac hvac₁ hevv hevSB he hinf hloc μ hμ
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  letI mV : ∀ v : Pl F, MeasurableSpace (κ → Fv F v) := fun _ => borel _
  haveI bV : ∀ v : Pl F, BorelSpace (κ → Fv F v) := fun _ => ⟨rfl⟩
  haveI := hμ
  obtain ⟨μi, hμi⟩ : ∃ μ : Measure (κ → mixedEmbedding.mixedSpace F), μ.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨μv, hμv, hμv1⟩ : ∃ μv : ∀ v : Pl F, Measure (κ → Fv F v), (∀ v, (μv v).IsAddHaarMeasure) ∧
      ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := by
    let K : ∀ v : Pl F, TopologicalSpace.PositiveCompacts (κ → Fv F v) := fun v =>
      ⟨⟨Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)),
        isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v⟩, by
          show (interior (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))).Nonempty
          rw [(isOpen_set_pi Set.finite_univ fun _ _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).interior_eq]
          exact ⟨0, fun i _ => (v.adicCompletionIntegers F).zero_mem⟩⟩
    refine ⟨fun v => Measure.addHaarMeasure (K v), fun v => inferInstance, fun v => ?_⟩
    have e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} = (K v : Set (κ → Fv F v)) := by
      ext x; simp [K]
    rw [e]
    exact Measure.addHaarMeasure_self
  haveI := hμv
  obtain ⟨c₀, -, hpure⟩ := GlobalTheory.T.integral_adelic_pureTensor_eq_product_local F κ μ μi μv hμv1
  obtain ⟨cI, hcI0, hcI⟩ := hinf
  choose C hC0 hC using hloc
  have hS : ∀ᶠ v in Filter.cofinite, vac v = GlobalTheory.RatWeilOp.ind κ v ∧ vac₁ v = GlobalTheory.RatWeilOp.ind κ v := hvac.and hvac₁
  set S₀ := (Filter.eventually_cofinite.1 hS).toFinset with hS₀
  have hout : ∀ v ∉ S₀, vac v = GlobalTheory.RatWeilOp.ind κ v ∧ vac₁ v = GlobalTheory.RatWeilOp.ind κ v := by
    intro v hv
    by_contra h
    exact hv (by simpa [hS₀] using h)
  have hind1 : ∀ v, ∫ t, GlobalTheory.RatWeilOp.ind κ v t * conj (GlobalTheory.RatWeilOp.ind κ v t) ∂(μv v) = 1 := fun v =>
    integral_ind v (μv v) (hμv1 v)
  have hC1 : ∀ v ∉ S₀, C v = 1 := by
    intro v hv
    obtain ⟨h1, h2⟩ := hout v hv
    have key := hC v (μv v) (hμv v) (vac v) (hvSB v) (vac v) (hvSB v)
    rw [hevv v, h2, h1, hind1 v, mul_one] at key
    exact_mod_cast key.symm
  set K : ℝ := cI * ∏ v ∈ S₀, C v with hK
  have hK0 : 0 ≤ K := mul_nonneg hcI0 (Finset.prod_nonneg fun v _ => hC0 v)
  have hsupC : Function.mulSupport (fun v => (C v : ℂ)) ⊆ (S₀ : Set (Pl F)) := by
    intro v hv
    by_contra h
    exact hv (by simp [hC1 v h])
  have hprodC : ∀ a : Pl F → ℂ, (Function.mulSupport a).Finite →
      ∏ᶠ v, ((C v : ℂ) * a v) = (∏ v ∈ S₀, (C v : ℂ)) * ∏ᶠ v, a v := by
    intro a ha
    rw [finprod_mul_distrib ((S₀.finite_toSet).subset hsupC) ha, finprod_eq_prod_of_mulSupport_subset _ hsupC]
  have hfam : ∀ φ : ∀ v : Pl F, (κ → Fv F v) → ℂ, (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in Filter.cofinite, φ v = vac v) →
      GlobalTheory.RatWeilOp.IsFam φ ∧ GlobalTheory.RatWeilOp.IsFam (fun v => ev v (φ v)) := by
    intro φ hSB hφ
    refine ⟨⟨hSB, ?_⟩, ⟨fun v => hevSB v _ (hSB v), ?_⟩⟩
    · filter_upwards [hφ, hvac] with v h1 h2
      rw [h1, h2]; rfl
    · filter_upwards [hφ, hvac₁] with v h1 h2
      rw [h1, hevv, h2]; rfl
  have hcross : ∀ (f f' : SInf F κ) (φ φ' : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in Filter.cofinite, φ v = vac v) → (∀ v, φ' v ∈ SB (κ → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ' v = vac v) →
      Integrable (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * conj (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' x)) μ ∧
      Integrable (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) (fun v => ev v (φ v)) x *
        conj (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f') (fun v => ev v (φ' v)) x)) μ ∧
      ∫ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) (fun v => ev v (φ v)) x *
        conj (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f') (fun v => ev v (φ' v)) x) ∂μ =
        (K : ℂ) * ∫ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * conj (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' x) ∂μ := by
    intro f f' φ φ' hs hφ hs' hφ'
    obtain ⟨a1, a2⟩ := hfam φ hs hφ
    obtain ⟨b1, b2⟩ := hfam φ' hs' hφ'
    obtain ⟨i1, e1⟩ := integral_pure_mul_conj μ μi μv c₀ hpure f f' φ φ' a1 b1
    obtain ⟨i2, e2⟩ := integral_pure_mul_conj μ μi μv c₀ hpure (ei f) (ei f') _ _ a2 b2
    refine ⟨i1, i2, ?_⟩
    have hloc' : ∀ v, ∫ t, ev v (φ v) t * conj (ev v (φ' v) t) ∂(μv v) =
        (C v : ℂ) * ∫ t, φ v t * conj (φ' v t) ∂(μv v) := fun v =>
      hC v (μv v) (hμv v) (φ v) (hs v) (φ' v) (hs' v)
    have hfin : (Function.mulSupport fun v => ∫ t, φ v t * conj (φ' v t) ∂(μv v)).Finite := by
      refine (Filter.eventually_cofinite.1 ((hφ.and hφ').and hvac)).subset fun v hv h => hv ?_
      show ∫ t, φ v t * conj (φ' v t) ∂(μv v) = 1
      rw [h.1.1, h.1.2, h.2]
      exact hind1 v
    rw [e2, e1, finprod_congr hloc', hprodC _ hfin, hcI μi hμi f f', hK]
    push_cast
    ring
  refine ⟨ENNReal.ofReal K, fun Φ hΦ => ?_⟩
  obtain ⟨T, m, f, φ, hSB, hT, rfl⟩ := GlobalTheory.SchADecomp.exists_sum_pure F κ Φ hΦ
  have hvacφ : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = vac v := fun i => by
    filter_upwards [hvac, T.finite_toSet.eventually_cofinite_notMem] with v h1 h2
    rw [hT i v h2, h1]
  have heΦ : e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) =
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) (fun v => ev v (φ i v)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => he _ _ (hSB i) (hvacφ i)
  rw [heΦ]
  have hexp : ∀ (g : Fin m → (κ → AF F) → ℂ) (x : κ → AF F),
      (∑ i, g i) x * conj ((∑ i, g i) x) = ∑ i, ∑ j, g i x * conj (g j x) := by
    intro g x
    simp only [Finset.sum_apply, map_sum, Finset.sum_mul_sum]
  have hint1 : ∀ i j, Integrable (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) x *
      conj (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f j) (φ j) x)) μ := fun i j =>
    (hcross (f i) (f j) (φ i) (φ j) (hSB i) (hvacφ i) (hSB j) (hvacφ j)).1
  have hint2 : ∀ i j, Integrable (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) (fun v => ev v (φ i v)) x *
      conj (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f j)) (fun v => ev v (φ j v)) x)) μ := fun i j =>
    (hcross (f i) (f j) (φ i) (φ j) (hSB i) (hvacφ i) (hSB j) (hvacφ j)).2.1
  have hI1 : Integrable (fun x => (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x *
      conj ((∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x)) μ :=
    (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint1 i j).congr
      (Filter.Eventually.of_forall fun x => (hexp _ x).symm)
  have hI2 : Integrable (fun x => (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) (fun v => ev v (φ i v))) x *
      conj ((∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) (fun v => ev v (φ i v))) x)) μ :=
    (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint2 i j).congr
      (Filter.Eventually.of_forall fun x => (hexp _ x).symm)
  rw [lintegral_sq_eq hI1, lintegral_sq_eq hI2, integral_congr_ae (Filter.Eventually.of_forall (hexp _)),
    integral_congr_ae (Filter.Eventually.of_forall (hexp _)),
    integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint1 i j,
    integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint2 i j]
  have hsum : ∀ i, ∫ x, ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) (fun v => ev v (φ i v)) x *
      conj (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f j)) (fun v => ev v (φ j v)) x) ∂μ =
      (K : ℂ) * ∫ x, ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) x * conj (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f j) (φ j) x) ∂μ := by
    intro i
    rw [integral_finset_sum _ fun j _ => hint2 i j, integral_finset_sum _ fun j _ => hint1 i j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ =>
      (hcross (f i) (f j) (φ i) (φ j) (hSB i) (hvacφ i) (hSB j) (hvacφ j)).2.2
  rw [Finset.sum_congr rfl fun i _ => hsum i, ← Finset.mul_sum, Complex.re_ofReal_mul, ENNReal.ofReal_mul hK0]

end GlobalTheory.TensorSquareIntegral
