import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponentsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdInt

theorem map_eq_smul_prod {ι Z Zi : Type} {Zv : ι → Type} [MeasurableSpace Z] [MeasurableSpace Zi]
    [∀ v, MeasurableSpace (Zv v)] (ρ : Measure Z) (mi : Measure Zi) (mv : ∀ v, Measure (Zv v))
    [SigmaFinite mi] [∀ v, SigmaFinite (mv v)] (pi : Z → Zi) (pv : ∀ v, Z → Zv v)
    (hpi : Measurable pi) (hpv : ∀ v, Measurable (pv v)) (S : Finset ι) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ (fi : Zi → ℝ≥0∞) (fv : ∀ v, Zv v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X, fi (pi X) * ∏ v ∈ S, fv v (pv v X) ∂ρ =
        (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * c) :
    ρ.map (fun X => (pi X, fun v : S => pv v X)) = c • mi.prod (Measure.pi fun v : S => mv v) := by
  classical
  have hT : Measurable (fun X => (pi X, fun v : S => pv v X)) :=
    hpi.prodMk (measurable_pi_lambda _ fun v => hpv v)
  by_cases hc0 : c = 0
  · have := h (fun _ => 1) (fun _ _ => 1) measurable_const (fun _ => measurable_const)
    simp only [hc0, mul_zero, Finset.prod_const_one, mul_one, lintegral_const, one_mul,
      Measure.measure_univ_eq_zero] at this
    simp [this, hc0]
  have key : mi.prod (Measure.pi fun v : S => mv v) =
      c⁻¹ • ρ.map (fun X => (pi X, fun v : S => pv v X)) := by
    refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
      (D := Set.pi Set.univ '' Set.pi Set.univ fun v : S => {s : Set (Zv v) | MeasurableSet s})
      MeasurableSpace.generateFrom_measurableSet generateFrom_pi
      MeasurableSpace.isPiSystem_measurableSet isPiSystem_pi mi.toFiniteSpanningSetsIn
      (Measure.FiniteSpanningSetsIn.pi fun v : S => (mv v).toFiniteSpanningSetsIn) ?_
    rintro s hs _ ⟨t, ht, rfl⟩
    have hs' : MeasurableSet s := hs
    have ht' : ∀ v : S, MeasurableSet (t v) := fun v => ht v (Set.mem_univ _)
    let fv : ∀ v, Zv v → ℝ≥0∞ := fun v => if hv : v ∈ S then (t ⟨v, hv⟩).indicator 1 else 0
    have hfv : ∀ v, Measurable (fv v) := by
      intro v
      by_cases hv : v ∈ S
      · simp only [fv, dif_pos hv]
        exact measurable_one.indicator (ht' _)
      · simp only [fv, dif_neg hv]
        exact measurable_zero
    have hfv' : ∀ v : S, fv v = (t v).indicator 1 := fun v => by simp only [fv, dif_pos v.2]
    have h1 := h (s.indicator 1) fv (measurable_one.indicator hs') hfv
    have hm : MeasurableSet (s ×ˢ Set.pi Set.univ t) :=
      hs'.prod (MeasurableSet.univ_pi ht')
    rw [Measure.smul_apply, Measure.map_apply hT hm, ← lintegral_indicator_one (hT hm), Measure.pi_pi]
    have h2 : ∀ X, ((fun X => (pi X, fun v : S => pv v X)) ⁻¹' (s ×ˢ Set.pi Set.univ t)).indicator
        (1 : Z → ℝ≥0∞) X = s.indicator 1 (pi X) * ∏ v ∈ S, fv v (pv v X) := by
      intro X
      rw [← Finset.prod_coe_sort S]
      simp only [hfv']
      by_cases hX : pi X ∈ s
      · by_cases hY : ∀ v : S, pv v X ∈ t v
        · rw [Set.indicator_of_mem (by simpa [hX] using hY)]
          simp [hX, hY]
        · rw [Set.indicator_of_notMem (by simpa [hX] using hY)]
          push_neg at hY
          obtain ⟨v, hv⟩ := hY
          rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])]
          simp
      · rw [Set.indicator_of_notMem (by simp [hX])]
        simp [hX]
    simp_rw [h2]
    rw [h1, ← Finset.prod_coe_sort S]
    simp only [hfv', lintegral_indicator_one hs', lintegral_indicator_one (ht' _), smul_eq_mul]
    rw [mul_comm c⁻¹, mul_assoc, ENNReal.mul_inv_cancel hc0 hc, mul_one]
  rw [key, smul_smul, ENNReal.mul_inv_cancel hc0 hc, one_smul]

theorem integral_tensor {ι Z Zi : Type} {Zv : ι → Type} [MeasurableSpace Z] [MeasurableSpace Zi]
    [∀ v, MeasurableSpace (Zv v)] (ρ : Measure Z) (mi : Measure Zi) (mv : ∀ v, Measure (Zv v))
    [SigmaFinite mi] [∀ v, SigmaFinite (mv v)] (pi : Z → Zi) (pv : ∀ v, Z → Zv v)
    (hpi : Measurable pi) (hpv : ∀ v, Measurable (pv v)) (S : Finset ι) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ (fi : Zi → ℝ≥0∞) (fv : ∀ v, Zv v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X, fi (pi X) * ∏ v ∈ S, fv v (pv v X) ∂ρ =
        (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * c)
    (Φi : Zi → ℂ) (Φv : ∀ v, Zv v → ℂ) (hi : Integrable Φi mi) (hv : ∀ v, Integrable (Φv v) (mv v)) :
    Integrable (fun X => Φi (pi X) * ∏ v ∈ S, Φv v (pv v X)) ρ ∧
      ∫ X, Φi (pi X) * ∏ v ∈ S, Φv v (pv v X) ∂ρ =
        (∫ Y, Φi Y ∂mi) * ((∏ v ∈ S, ∫ Y, Φv v Y ∂(mv v)) * (c.toReal : ℂ)) := by
  have hT : Measurable (fun X => (pi X, fun v : S => pv v X)) :=
    hpi.prodMk (measurable_pi_lambda _ fun v => hpv v)
  have hmap := map_eq_smul_prod ρ mi mv pi pv hpi hpv S c hc h
  let G : Zi × (∀ v : S, Zv v) → ℂ := fun Y => Φi Y.1 * ∏ v : S, Φv v (Y.2 v)
  have hG : Integrable G (mi.prod (Measure.pi fun v : S => mv v)) :=
    hi.mul_prod (Integrable.fintype_prod_dep (f := fun v : S => Φv v) fun v => hv v)
  have hG' : Integrable G (ρ.map (fun X => (pi X, fun v : S => pv v X))) := by
    rw [hmap]; exact hG.smul_measure hc
  have he : (fun X => Φi (pi X) * ∏ v ∈ S, Φv v (pv v X)) =
      G ∘ (fun X => (pi X, fun v : S => pv v X)) := by
    funext X
    simp only [G, Function.comp]
    rw [← Finset.prod_coe_sort S]
  rw [he]
  refine ⟨(integrable_map_measure hG'.aestronglyMeasurable hT.aemeasurable).1 hG', ?_⟩
  have := integral_map hT.aemeasurable hG'.aestronglyMeasurable
  simp only [Function.comp_def]
  rw [← this, hmap, integral_smul_measure]
  simp only [G]
  rw [integral_prod_mul Φi (fun Y : ∀ v : S, Zv v => ∏ v : S, Φv v (Y v)),
    integral_fintype_prod_eq_prod (fun v : S => Φv v), ← Finset.prod_coe_sort S, Complex.real_smul]
  ring

theorem hasProd_of_tail {ι : Type} (f : ι → ℂ) (a : ι → ℝ) (ha : ∀ v, 0 ≤ a v)
    (hs : Summable fun v => |a v - 1|) (S : Finset ι) (hf : ∀ v ∉ S, f v = a v) :
    HasProd f ((∏ v ∈ S, f v) *
      (((ENNReal.ofReal (∏' v : {v // v ∉ S}, a v.1)).toReal : ℝ) : ℂ)) := by
  have hm : Multipliable fun v : {v // v ∉ S} => a v.1 := by
    have h1 : Summable fun v : {v // v ∉ S} => ‖a v.1 - 1‖ := hs.subtype _
    simpa using multipliable_one_add_of_summable h1
  have h0 : 0 ≤ ∏' v : {v // v ∉ S}, a v.1 :=
    ge_of_tendsto' hm.hasProd fun s => Finset.prod_nonneg fun v _ => ha _
  rw [ENNReal.toReal_ofReal h0]
  have h2 := hm.hasProd.map Complex.ofRealHom Complex.continuous_ofReal
  refine (S.hasProd f).mul_compl ?_
  have h3 : (f ∘ Subtype.val : {v // v ∉ S} → ℂ) = Complex.ofRealHom ∘ fun v : {v // v ∉ S} => a v.1 :=
    funext fun v => hf v.1 v.2
  have h4 : HasProd (f ∘ Subtype.val : {v // v ∉ S} → ℂ)
      ((∏' v : {v // v ∉ S}, a v.1 : ℝ) : ℂ) := by rw [h3]; exact h2
  exact h4

theorem integral_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b' Φf Φv → IsProdInfFin Φ Φinf Φf → Integrable Φ ν ∧ Multipliable (fun v => ∫ X, Φv v X ∂(mv v)) ∧ ∫ X, Φ X ∂ν = (∫ X, Φinf X ∂mi) * ∏' v, ∫ X, Φv v X ∂(mv v) := by
  intro F E _ _ _ _ _ d b n M ν mi mv hP d' b' Φ Φinf Φf Φv hc hcs hpure hΦ
  obtain ⟨⟨hmi, hmv, hsum⟩, hP⟩ := hP
  obtain ⟨hsb, hae, hfin⟩ := hpure
  obtain ⟨hco, -, hint, hbb⟩ := GlobalTheory.GaugeEx.IntBasis.main F E (AlgHom.id F E) d b
  obtain ⟨-, -, hci, hcv⟩ := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hae' : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 := by
    filter_upwards [hae, hbb d' b'] with v h1 h2
    rw [h1]
    congr 1
    ext Y
    rw [mem_latV_iff, mem_latV_iff, h2]
  have hfinS := Filter.eventually_cofinite.1 hae'
  set S := hfinS.toFinset with hS
  have hout : ∀ v ∉ S, Φv v = (latV b v).indicator 1 := by
    intro v hv
    by_contra hne
    exact hv (by simpa [hS] using hne)
  have hlat : ∀ v : HeightOneSpectrum (𝓞 F),
      IsClosed (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    have : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
        ⋂ a, ⋂ i, (fun Y => Y a i) ⁻¹' intV b v := by
      ext Y; simp [mem_latV_iff]
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun i =>
      (hco v).1.isClosed.preimage (by fun_prop)
  set B : Set (Fin n → Fin M → AF F ⊗[F] E) := {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v} with hB
  have hBm : MeasurableSet B := by
    have : B = ⋂ v, ⋂ (_ : v ∉ S), (fun X => projV v (projFin X)) ⁻¹' latV b v := by
      ext X; simp [hB]
    rw [this]
    exact (isClosed_iInter fun v => isClosed_iInter fun _ => (hlat v).preimage (hcv v)).measurableSet
  have hΦB : Φ = B.indicator fun X => Φinf (projInf X) * ∏ v ∈ S, Φv v (projV v (projFin X)) := by
    funext X
    rw [hΦ X, hfin]
    by_cases hX : X ∈ B
    · rw [Set.indicator_of_mem hX, finprod_eq_prod_of_mulSupport_subset (s := S)]
      intro v hv
      by_contra hvS
      have hvS' : v ∉ S := hvS
      apply hv
      simp only [hout v hvS']
      exact Set.indicator_of_mem (hX v hvS') _
    · rw [Set.indicator_of_notMem hX]
      simp only [hB, Set.mem_setOf_eq, not_forall] at hX
      obtain ⟨v, hvS, hv⟩ := hX
      have hev : ∀ᶠ v in Filter.cofinite, Φv v (projV v (projFin X)) = 1 := by
        have h1 : ∀ᶠ v in Filter.cofinite, ∀ a i, prV v (X a i) ∈ intV b v :=
          Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i => hint _
        filter_upwards [hae', h1] with w h2 h3
        rw [h2]
        exact Set.indicator_of_mem (show projV w (projFin X) ∈ latV b w from h3) _
      rw [finprod_eq_zero _ v (by rw [hout v hvS]; exact Set.indicator_of_notMem hv _)
        (Filter.eventually_cofinite.1 hev), mul_zero]
  haveI : SigmaFinite mi := inferInstance
  haveI : ∀ v, SigmaFinite (mv v) := fun v => inferInstance
  obtain ⟨h1, h2⟩ := integral_tensor (ν.restrict B) mi mv projInf (fun v X => projV v (projFin X))
    hci.measurable (fun v => (hcv v).measurable) S (tailProd b mv S) ENNReal.ofReal_ne_top (hP S)
    Φinf Φv (hc.integrable_of_hasCompactSupport hcs)
    (fun v => (hsb v).1.continuous.integrable_of_hasCompactSupport (hsb v).2)
  have h3 := hasProd_of_tail (fun v => ∫ X, Φv v X ∂(mv v)) (fun v => (mv v (latV b v)).toReal)
    (fun v => ENNReal.toReal_nonneg) hsum S (by
      intro v hv
      rw [hout v hv]
      have := integral_indicator_const (μ := mv v) (1 : ℂ) (hlat v).measurableSet
      simpa [Measure.real, Pi.one_def] using this)
  refine ⟨?_, h3.multipliable, ?_⟩
  · rw [hΦB]; exact (integrable_indicator_iff hBm).2 h1
  · rw [h3.tprod_eq, hΦB, integral_indicator hBm, h2]
    rfl

end GlobalTheory.GaugeEx.ProdInt
