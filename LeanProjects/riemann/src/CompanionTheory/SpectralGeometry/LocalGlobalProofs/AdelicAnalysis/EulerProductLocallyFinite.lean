import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.EulerInt

theorem map_eq_prod {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype ι]
    {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (I : Measure X) (μ₀ : Measure Y) (μ : ∀ i, Measure (Z i)) [SigmaFinite μ₀]
    [∀ i, SigmaFinite (μ i)] (c : ℝ≥0) (P : X → Y × ∀ i, Z i) (hP : Measurable P)
    (h : ∀ (A : Set Y) (B : ∀ i, Set (Z i)), MeasurableSet A → (∀ i, MeasurableSet (B i)) →
      I (P ⁻¹' (A ×ˢ Set.univ.pi B)) = (c : ℝ≥0∞) * (μ₀ A * ∏ i, μ i (B i))) :
    I.map P = (c • μ₀).prod (Measure.pi μ) := by
  symm
  refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
    (D := Set.univ.pi '' Set.univ.pi fun i => {s | MeasurableSet s})
    MeasurableSpace.generateFrom_measurableSet generateFrom_pi
    MeasurableSpace.isPiSystem_measurableSet isPiSystem_pi
    ((c • μ₀).toFiniteSpanningSetsIn)
    (Measure.FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn) ?_
  rintro s hs _ ⟨B, hB, rfl⟩
  have hB' : ∀ i, MeasurableSet (B i) := fun i => hB i (Set.mem_univ i)
  rw [Measure.map_apply hP (hs.prod (MeasurableSet.univ_pi hB')), h s B hs hB', Measure.pi_pi]
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_assoc]

theorem integral_box {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype ι]
    {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (I : Measure X) (μ₀ : Measure Y) (μ : ∀ i, Measure (Z i)) [SigmaFinite μ₀]
    [∀ i, SigmaFinite (μ i)] (c : ℝ≥0) (P : X → Y × ∀ i, Z i) (hP : Measurable P)
    (h : ∀ (A : Set Y) (B : ∀ i, Set (Z i)), MeasurableSet A → (∀ i, MeasurableSet (B i)) →
      I (P ⁻¹' (A ×ˢ Set.univ.pi B)) = (c : ℝ≥0∞) * (μ₀ A * ∏ i, μ i (B i)))
    (f₀ : Y → ℂ) (f : ∀ i, Z i → ℂ) (hf₀ : Integrable f₀ μ₀) (hf : ∀ i, Integrable (f i) (μ i)) :
    Integrable (fun x => f₀ (P x).1 * ∏ i, f i ((P x).2 i)) I ∧
      ∫ x, f₀ (P x).1 * ∏ i, f i ((P x).2 i) ∂I =
        (c : ℂ) * ((∫ y, f₀ y ∂μ₀) * ∏ i, ∫ z, f i z ∂(μ i)) := by
  have hmap := map_eq_prod I μ₀ μ c P hP h
  set g : (Y × ∀ i, Z i) → ℂ := fun z => f₀ z.1 * ∏ i, f i (z.2 i) with hg
  have hgi : Integrable g ((c • μ₀).prod (Measure.pi μ)) :=
    Integrable.mul_prod (hf₀.smul_measure_nnreal) (Integrable.fintype_prod_dep hf)
  rw [← hmap] at hgi
  refine ⟨(integrable_map_measure hgi.aestronglyMeasurable hP.aemeasurable).1 hgi, ?_⟩
  have h1 : ∫ x, g (P x) ∂I = ∫ z, g z ∂(I.map P) :=
    (integral_map hP.aemeasurable hgi.aestronglyMeasurable).symm
  have h2 : ∫ z, g z ∂((c • μ₀).prod (Measure.pi μ)) =
      (∫ y, f₀ y ∂(c • μ₀)) * ∫ z : (∀ i, Z i), ∏ i, f i (z i) ∂(Measure.pi μ) :=
    integral_prod_mul f₀ (fun z : (∀ i, Z i) => ∏ i, f i (z i))
  change ∫ x, g (P x) ∂I = _
  rw [h1, hmap, h2, integral_fintype_prod_eq_prod, integral_smul_nnreal_measure]
  simp [NNReal.smul_def, mul_assoc]

variable (F : Type) [Field F] [NumberField F]

theorem infinite_adeles_t2Space : T2Space (Ainf F) :=
  inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))

theorem sc_ainf (h : SecondCountableTopology (AF F)) : SecondCountableTopology (Ainf F) := by
  have h' : SecondCountableTopology (Ainf F × Af F) := h
  have he : IsEmbedding (fun x : Ainf F => ((x, 0) : Ainf F × Af F)) :=
    isEmbedding_prodMkLeft 0
  exact he.secondCountableTopology

end GlobalTheory.CompanionTheory.SW.EulerInt

namespace GlobalTheory.CompanionTheory.SW.EulerInt

theorem finprod_eq_indicator {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d n M : ℕ}
    (b : Module.Basis (Fin d) F E)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v, v ∉ S → Φv v = (latV b v).indicator 1)
    (hae : ∀ X : (Fin n → Fin M → Af F ⊗[F] E), ∀ᶠ v in Filter.cofinite, projV v X ∈ latV b v)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    ∏ᶠ v, Φv v (projV v (projFin X)) =
      (intOff b S).indicator (fun Y => ∏ v ∈ S, Φv v (projV v (projFin Y))) X := by
  classical
  by_cases hX : X ∈ intOff b S
  · rw [Set.indicator_of_mem hX]
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro v hv
    by_contra hvS
    apply hv
    have hvS' : v ∉ S := by simpa using hvS
    simp only [hS v hvS']
    exact Set.indicator_of_mem (hX v hvS') _
  · rw [Set.indicator_of_notMem hX]
    have : ∃ v, v ∉ S ∧ projV v (projFin X) ∉ latV b v := by
      by_contra hne
      push Not at hne
      exact hX hne
    obtain ⟨v, hvS, hv⟩ := this
    refine finprod_eq_zero _ v ?_ ?_
    · simp only [hS v hvS]
      exact Set.indicator_of_notMem hv _
    · have hfin : {w | projV w (projFin X) ∉ latV b w}.Finite :=
        Filter.eventually_cofinite.1 (hae (projFin X))
      refine (hfin.union S.finite_toSet).subset ?_
      intro w hw
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
      apply hw
      simp only [hS w hc.2]
      exact Set.indicator_of_mem hc.1 _

end GlobalTheory.CompanionTheory.SW.EulerInt

theorem GlobalTheory.CompanionTheory.SW.EulerInt.euler_int : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → IsLocallyFiniteMeasure minf → (∀ v, IsLocallyFiniteMeasure (m v)) → ∀ (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf → Measurable Φ ∧ Integrable Φ I ∧ Multipliable (fun v => ∫ X, Φv v X ∂(m v)) ∧ ∫ X, Φ X ∂I = (∫ X, Φinf X ∂minf) * ∏' v, ∫ X, Φv v X ∂(m v) := by
  intro F E _ _ _ _ _ σ hCM d b n M I minf m hEu hminf hm Φ Φinf Φf Φv hc hcs hpure hprod
  classical
  obtain ⟨hpi, hpf, hpv, hlat, hint, hae, -, -, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  haveI := lcA
  haveI := scA
  haveI := t2A
  haveI : T2Space (Ainf F) := GlobalTheory.CompanionTheory.SW.EulerInt.infinite_adeles_t2Space F
  haveI : SecondCountableTopology (Ainf F) := GlobalTheory.CompanionTheory.SW.EulerInt.sc_ainf F scA
  have KA := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  have KI := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := KI.2.2.1
  haveI : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := KA.2.2.2.2.2.2.2.1 n M
  haveI : BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := KI.2.2.2.2.2.2.2.1 n M
  have KVb : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (Fv F v ⊗[F] E) ∧
      BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := by
    intro v
    obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    have K := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)
    exact ⟨K.2.2.1, K.2.2.2.2.2.2.2.1 n M⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (Fv F v ⊗[F] E) := fun v => (KVb v).1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => (KVb v).2
  haveI : SigmaFinite minf := inferInstance
  haveI : ∀ v, SigmaFinite (m v) := fun v => inferInstance
  obtain ⟨-, hsum, S₀, hEP⟩ := hEu
  have hbad := hpure.2.1
  let S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ (Filter.eventually_cofinite.1 hbad).toFinset
  have hS : ∀ v, v ∉ S → Φv v = (latV b v).indicator 1 := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_right _ (by simpa using h))
  have hSS : S₀ ⊆ S := Finset.subset_union_left
  let Ψ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ :=
    fun Y => Φinf (projInf Y) * ∏ v ∈ S, Φv v (projV v (projFin Y))
  have hΦ : Φ = (intOff b S).indicator Ψ := by
    funext X
    rw [hprod X, hpure.2.2 (projFin X), GlobalTheory.CompanionTheory.SW.EulerInt.finprod_eq_indicator b Φv S hS hae X]
    by_cases hX : X ∈ intOff b S
    · simp [Set.indicator_of_mem hX, Ψ]
    · simp [Set.indicator_of_notMem hX]
  have hcv : ∀ v, Continuous (Φv v) := fun v => (hpure.1 v).1.continuous
  have hΨc : Continuous Ψ :=
    (hc.comp hpi).mul (continuous_finset_prod _ fun v _ => (hcv v).comp ((hpv v).comp hpf))
  have hmI : MeasurableSet (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := (hint S).measurableSet
  let a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (m v (latV b v)).toReal
  have hmul : Multipliable (fun v : {v // v ∉ S} => a v.1) :=
    ((GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod _ a hsum).2.1 S).1
  have hT0 : 0 ≤ ∏' v : {v // v ∉ S}, a v.1 :=
    GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg hmul fun _ => ENNReal.toReal_nonneg
  let c : ℝ≥0 := ⟨∏' v : {v // v ∉ S}, a v.1, hT0⟩
  let P : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E) ×
      ∀ i : S, (Fin n → Fin M → Fv F i.1 ⊗[F] E) :=
    fun X => (projInf X, fun i => projV i.1 (projFin X))
  have hP : Measurable P :=
    hpi.measurable.prodMk (measurable_pi_lambda _ fun i => ((hpv i.1).comp hpf).measurable)
  have hbox : ∀ (A : Set (Fin n → Fin M → Ainf F ⊗[F] E))
      (B : ∀ i : S, Set (Fin n → Fin M → Fv F i.1 ⊗[F] E)), MeasurableSet A →
      (∀ i, MeasurableSet (B i)) →
      (I.restrict (intOff b S)) (P ⁻¹' (A ×ˢ Set.univ.pi B)) =
        (c : ℝ≥0∞) * (minf A * ∏ i : S, m i.1 (B i)) := by
    intro A B hA hB
    let φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞ := A.indicator 1
    let φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞ :=
      fun v => if h : v ∈ S then (B ⟨v, h⟩).indicator 1 else 0
    have hφS : ∀ i : S, φ i.1 = (B i).indicator 1 := fun i => by simp [φ]
    have hφm : ∀ v, Measurable (φ v) := by
      intro v
      by_cases h : v ∈ S
      · rw [hφS ⟨v, h⟩]
        exact measurable_one.indicator (hB _)
      · simp only [φ, dif_neg h]
        exact measurable_const
    have e := hEP S hSS φinf φ (measurable_one.indicator hA) hφm
    have hPm : MeasurableSet (P ⁻¹' (A ×ˢ Set.univ.pi B)) :=
      hP (hA.prod (MeasurableSet.univ_pi hB))
    have hl : pureL b S φinf φ = (P ⁻¹' (A ×ˢ Set.univ.pi B) ∩ intOff b S).indicator 1 := by
      funext X
      have hpr : ∏ v ∈ S, φ v (projV v (projFin X)) =
          ∏ i : S, (B i).indicator (1 : (Fin n → Fin M → Fv F i.1 ⊗[F] E) → ℝ≥0∞) (projV i.1 (projFin X)) := by
        rw [← Finset.prod_coe_sort S (fun v => φ v (projV v (projFin X)))]
        exact Finset.prod_congr rfl fun i _ => by rw [hφS i]
      unfold pureL
      by_cases hX : X ∈ intOff b S
      · rw [Set.indicator_of_mem hX, hpr]
        by_cases hPX : P X ∈ A ×ˢ Set.univ.pi B
        · rw [Set.indicator_of_mem (show X ∈ _ ∩ _ from ⟨hPX, hX⟩)]
          have h1 : projInf X ∈ A := hPX.1
          have h2 : ∀ i : S, projV i.1 (projFin X) ∈ B i := fun i => hPX.2 i (Set.mem_univ i)
          simp [φinf, h1, h2]
        · rw [Set.indicator_of_notMem (fun h => hPX h.1)]
          by_cases h1 : projInf X ∈ A
          · have h2 : ¬ ∀ i : S, projV i.1 (projFin X) ∈ B i := fun h2 =>
              hPX ⟨h1, fun i _ => h2 i⟩
            push Not at h2
            obtain ⟨i, hi⟩ := h2
            rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _), mul_zero]
          · simp [φinf, h1]
      · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (fun h => hX h.2)]
    have e1 : ∫⁻ X, φinf X ∂minf = minf A := lintegral_indicator_one hA
    have e2 : ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v) = ∏ i : S, m i.1 (B i) := by
      rw [← Finset.prod_coe_sort S (fun v => ∫⁻ X, φ v X ∂(m v))]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hφS i]
      exact lintegral_indicator_one (hB i)
    rw [hl, lintegral_indicator_one (hPm.inter hmI), e1, e2,
      ENNReal.ofReal_eq_coe_nnreal hT0] at e
    rw [Measure.restrict_apply hPm, e]
    simp only [ENNReal.coe_one, one_mul]
    exact mul_comm _ _
  have hinf : Integrable Φinf minf := hc.integrable_of_hasCompactSupport hcs
  have hvi : ∀ v, Integrable (Φv v) (m v) := fun v =>
    (hcv v).integrable_of_hasCompactSupport (hpure.1 v).2
  obtain ⟨hI, hInt⟩ := GlobalTheory.CompanionTheory.SW.EulerInt.integral_box
    (Z := fun i : S => Fin n → Fin M → Fv F i.1 ⊗[F] E)
    (I.restrict (intOff b S)) minf (fun i : S => m i.1) c P hP hbox Φinf (fun i => Φv i.1) hinf
    (fun i => hvi i.1)
  have hΨeq : (fun X => Φinf (P X).1 * ∏ i : S, Φv i.1 ((P X).2 i)) = Ψ := by
    funext X
    exact congrArg (Φinf (projInf X) * ·)
      (Finset.prod_coe_sort S (fun v => Φv v (projV v (projFin X))))
  rw [hΨeq] at hInt hI
  have hvS : ∀ v, v ∉ S → ∫ X, Φv v X ∂(m v) = ((a v : ℝ) : ℂ) := by
    intro v hv
    have hl : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
      (hlat v).2.measurableSet
    rw [hS v hv]
    have := integral_indicator_const (μ := m v) (1 : ℂ) hl
    change ∫ X, (latV b v).indicator (fun _ => (1 : ℂ)) X ∂(m v) = _
    simpa [Measure.real, a] using this
  have hHP : HasProd (fun v => ∫ X, Φv v X ∂(m v))
      ((∏ v ∈ S, ∫ X, Φv v X ∂(m v)) * ((∏' v : {v // v ∉ S}, a v.1 : ℝ) : ℂ)) := by
    refine HasProd.mul_isCompl (s := (S : Set (HeightOneSpectrum (𝓞 F)))) (t := (S : Set _)ᶜ)
      isCompl_compl (S.hasProd _) ?_
    have h := hmul.hasProd.map Complex.ofRealHom Complex.continuous_ofReal
    have hfun : ((fun v => ∫ X, Φv v X ∂(m v)) ∘ Subtype.val :
          ↥((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) → ℂ) =
        (Complex.ofRealHom ∘ fun v : {v // v ∉ S} => a v.1) := by
      funext v
      exact hvS v.1 v.2
    rw [hfun]
    exact h
  refine ⟨?_, ?_, hHP.multipliable, ?_⟩
  · rw [hΦ]
    exact hΨc.measurable.indicator hmI
  · rw [hΦ]
    exact (integrable_indicator_iff hmI).2 hI
  · rw [hHP.tprod_eq, hΦ, integral_indicator hmI, hInt,
      Finset.prod_coe_sort S (fun v => ∫ X, Φv v X ∂(m v))]
    have hcc : ((c : ℝ) : ℂ) = ((∏' v : {v // v ∉ S}, a v.1 : ℝ) : ℂ) := rfl
    rw [hcc]
    ring
