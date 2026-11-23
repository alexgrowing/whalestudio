import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponentsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticUnitaryLocalComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableSetOrbitExistsMeasurableSectionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepPairMeasureFiniteOnCompactsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WittTheoremAdelicOneVectorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralWittTheoremAlmostAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaChangeSetsOutsideFiniteSetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductTailSplitFiniteFactorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TailProdMulOfLatticeMassMulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralOrthogonalComplementPairIndepGroupElemeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyIntegralOrthogonalComplementPairStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticFormOrbitRationalVectorEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentsAdelicUnitaryElementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousUnitaryTwoStepVectorAndTranslatePairStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.TsProd

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem measurableSet_latV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (n M : ℕ) :
    MeasurableSet (latV (n := n) (M := M) b v) := by
  have h := ((GlobalTheory.T.integralPointsFinitePlaceTensor_properties F E σ d b).1 v).2
  have : latV (n := n) (M := M) b v = ⋂ a, ⋂ i, (fun Y => Y a i) ⁻¹' intV b v := by
    ext Y; simp [mem_latV_iff]
  rw [this]
  refine IsOpen.measurableSet ?_
  exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => h.preimage (by fun_prop)

theorem isProd_of_large (σ : E →ₐ[F] E) {n M : ℕ} (ν : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (hc : Conv b mi mv)
    (h : ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), S₀ ⊆ S →
      ∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
      (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞),
      Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v},
        fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν =
      (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S) :
    IsProd b ν mi mv := by
  classical
  refine ⟨hc, fun S fi fv hfi hfv => ?_⟩
  have h1 : ∀ v, v ∈ S ∪ S₀ ↔ v ∈ S ∨ v ∈ S₀ \ S := by intro v; simp; tauto
  have h2 : Disjoint S (S₀ \ S) := Finset.disjoint_sdiff
  rw [GlobalTheory.T.restrictedProduct_tail_split_finite_factors F E d b n M mi mv S (S₀ \ S) (S ∪ S₀) hc h1 h2]
  exact GlobalTheory.T.product_formula_change_sets_outside_finite_set F E d b n M ν mi mv S (S₀ \ S) (S ∪ S₀) (fun v => latV b v) h1 h2
    (fun v => measurableSet_latV b σ v n M) (fun _ _ => rfl)
    (h _ Finset.subset_union_right) fi fv hfi hfv

theorem isProd_sets {n M : ℕ} {ν : Measure (Fin n → Fin M → AF F ⊗[F] E)}
    {mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)}
    {mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)}
    (h : IsProd b ν mi mv) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) (hAe : ∀ᶠ v in Filter.cofinite, A v = latV b v)
    (hAm : ∀ v ∉ S, mv v (A v) = mv v (latV b v))
    (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞)
    (hfi : Measurable fi) (hfv : ∀ v, Measurable (fv v)) :
    ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ A v},
        fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν =
      (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S := by
  classical
  have hfin : {v | ¬ A v = latV b v}.Finite := hAe
  set S₀ := hfin.toFinset with hS₀
  have h1 : ∀ v, v ∈ S ∪ S₀ ↔ v ∈ S ∨ v ∈ S₀ \ S := by intro v; simp; tauto
  have h2 : Disjoint S (S₀ \ S) := Finset.disjoint_sdiff
  rw [GlobalTheory.T.restrictedProduct_tail_split_finite_factors F E d b n M mi mv S (S₀ \ S) (S ∪ S₀) h.1 h1 h2,
    GlobalTheory.T.product_formula_change_sets_outside_finite_set F E d b n M ν mi mv S (S₀ \ S) (S ∪ S₀) A h1 h2 hA
    (fun v hv => by
      by_contra hne
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hne)))
    (h.2 _) fi fv hfi hfv]
  congr 2
  exact Finset.prod_congr rfl fun v hv => hAm v (Finset.mem_sdiff.1 hv).2

include b in
theorem measurableSet_cyl {n M : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) :
    MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v ∉ S, projV v (projFin X) ∈ A v} := by
  have hc : Countable (HeightOneSpectrum (𝓞 F)) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have : {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v ∉ S, projV v (projFin X) ∈ A v} =
      ⋂ v, ⋂ (_ : v ∉ S), (fun X => projV v (projFin X)) ⁻¹' A v := by
    ext X; simp
  rw [this]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
    ((GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M).2.2.2 v).measurable (hA v)

end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
  {a : F} {B : Matrix (Fin (M + 1)) (Fin M) E} {J' : Matrix (Fin M) (Fin M) E}

section
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]

theorem measurable_pair (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (g : HA R σ J) :
    Measurable fun y' => pairOf R σ J B y g y' :=
  ((GlobalTheory.T.continuous_unitaryTwoStepVectorAndTranslatePair F E σ R M J B).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).measurable

theorem exists_sec (x : Fin 1 → Fin (M + 1) → E) :
    MeasurableSet {y : Fin 1 → Fin (M + 1) → R ⊗[F] E | ∃ g : HA R σ J, g • ratTup (F := F) R x = y} ∧
    ∃ s, IsSec R σ J x s ∧ ∀ (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), IsFiniteMeasureOnCompacts m' →
      ∀ f : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f →
        Measurable fun y => ∫⁻ y', f (pairOf R σ J B y (s y) y') ∂m' := by
  obtain ⟨h1, s, hs, hs'⟩ := GlobalTheory.T.measurableSet_orbit_exists_measurable_section (HA R σ J) (Fin 1 → Fin (M + 1) → R ⊗[F] E) (ratTup (F := F) R x)
  refine ⟨h1, s, hs', fun m' hm' f hf => ?_⟩
  have hm : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin 1 → Fin M → R ⊗[F] E) =>
      f (pairOf R σ J B p.1 (s p.1) p.2) :=
    hf.comp ((GlobalTheory.T.continuous_unitaryTwoStepVectorAndTranslatePair F E σ R M J B).measurable.comp
      (measurable_fst.prodMk ((hs.comp measurable_fst).prodMk measurable_snd)))
  exact hm.lintegral_prod_right'

end

variable {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem fst_mem {v : HeightOneSpectrum (𝓞 F)} {y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E}
    {g : HA (Fv F v) σ J} {y' : Fin 1 → Fin M → Fv F v ⊗[F] E}
    (h : pairOf (Fv F v) σ J B y g y' ∈ latV b v) : y ∈ latV b v := by
  intro c i k
  have := h 0 i k
  rw [Subsingleton.elim c 0]
  exact this

theorem good_ae (hCM : IsCMExt F E σ) (hS : StepData σ J x a B J') :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ m' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E), IsInvTup (Fv F v) σ J' m' →
      ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (g : HA (Fv F v) σ J),
        g • ratTup (F := F) (Fv F v) x = y → y ∈ latV b v →
        m' {y' | pairOf (Fv F v) σ J B y g y' ∈ latV b v} = m' (latV b v) := by
  filter_upwards [GlobalTheory.T.eventually_integral_orthogonalComplement_pair F E σ d b M J x a B J' hS,
    GlobalTheory.T.integral_witt_theorem_almost_all_places F E σ hCM d b (M + 1) J x a hS.1 hS.2.1 hS.2.2.1] with v h1 h2 m' hm' y g hg hy
  obtain ⟨k, hk, hk'⟩ := h2 y hy (hg ▸ GlobalTheory.T.hermitian_quadratic_form_orbit_rational_vector_eq F E σ hCM _ _ J x a hS.2.2.1 g)
  have hL := measurableSet_latV b σ v 2 (M + 1)
  have h3 := GlobalTheory.T.lintegral_orthogonalComplement_pair_indep_groupElement F E σ hCM (Fv F v) M J x a B J' m' hS hm' y g k (hg.trans hk.symm)
    ((latV b v).indicator 1) (measurable_one.indicator hL)
  have h4 : ∀ g : HA (Fv F v) σ J, ∫⁻ y', (latV b v).indicator (1 : (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (pairOf (Fv F v) σ J B y g y') ∂m' =
      m' {y' | pairOf (Fv F v) σ J B y g y' ∈ latV b v} := by
    intro g
    exact lintegral_indicator_one (measurable_pair (B := B) (Fv F v) y g hL)
  rw [h4, h4] at h3
  rw [h3]
  congr 1
  ext y'
  simp [h1 k hk' y y', hy]

theorem mass_mul {v : HeightOneSpectrum (𝓞 F)} {m : Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E)}
    {m' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)} {N : Measure (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E)}
    (hm : OnOrbit (Fv F v) σ J x m) (hN : TwoStep (Fv F v) σ J x B m m' N)
    (h : ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (g : HA (Fv F v) σ J),
        g • ratTup (F := F) (Fv F v) x = y → y ∈ latV b v →
        m' {y' | pairOf (Fv F v) σ J B y g y' ∈ latV b v} = m' (latV b v)) :
    N (latV b v) = m (latV b v) * m' (latV b v) := by
  obtain ⟨-, s, hs, -⟩ := exists_sec (σ := σ) (J := J) (B := B) (Fv F v) x
  have hL := measurableSet_latV b σ v 2 (M + 1)
  have h1 := hN ((latV b v).indicator 1) (measurable_one.indicator hL) s hs
  rw [lintegral_indicator_one hL] at h1
  rw [h1, mul_comm, ← setLIntegral_const, ← lintegral_indicator (measurableSet_latV b σ v 1 (M + 1))]
  refine lintegral_congr_ae ?_
  have hm' : ∀ᵐ y ∂m, ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) x = y := hm
  filter_upwards [hm'] with y hy
  have h4 : ∫⁻ y', (latV b v).indicator (1 : (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (pairOf (Fv F v) σ J B y (s y) y') ∂m' =
      m' {y' | pairOf (Fv F v) σ J B y (s y) y' ∈ latV b v} := by
    exact lintegral_indicator_one (measurable_pair (B := B) (Fv F v) y (s y) hL)
  rw [h4]
  by_cases hyL : y ∈ latV b v
  · rw [Set.indicator_of_mem hyL, h y (s y) (hs y hy) hyL]
  · rw [Set.indicator_of_notMem hyL]
    have : {y' | pairOf (Fv F v) σ J B y (s y) y' ∈ latV b v} = ∅ :=
      Set.eq_empty_of_forall_notMem fun y' hy' => hyL (fst_mem b hy')
    rw [this, measure_empty]

theorem adelic_orbit (hCM : IsCMExt F E σ) (hS : StepData σ J x a B J')
    {ν : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)}
    {mi : Measure (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E)}
    {mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E)}
    (h : IsProd b ν mi mv) (hi : OnOrbit (Ainf F) σ J x mi) (hv : ∀ v, OnOrbit (Fv F v) σ J x (mv v)) :
    ∀ᵐ y ∂ν, ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y := by
  have h1 := (GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 1 (M + 1) ν mi mv h).2.2.2
    {y | ∃ g : HA (Ainf F) σ J, g • ratTup (F := F) (Ainf F) x = y}
    (fun v => {y | ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) x = y})
    (exists_sec (σ := σ) (J := J) (B := B) (Ainf F) x).1
    (fun v => (exists_sec (σ := σ) (J := J) (B := B) (Fv F v) x).1) hi hv
  have h2 : ∀ᵐ y ∂ν, projInf y ∈ {y | ∃ g : HA (Ainf F) σ J, g • ratTup (F := F) (Ainf F) x = y} ∧
      ∀ v, projV v (projFin y) ∈ {y | ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) x = y} := h1
  filter_upwards [h2] with y ⟨⟨gi, hgi⟩, hy⟩
  refine GlobalTheory.T.witt_theorem_adelic_one_vector F E σ hCM (M + 1) J x a hS.1 hS.2.1 hS.2.2.1 y ?_
  refine ((q_and_unitary_local_components F E σ (M + 1) J).1 (y 0) a).2 ⟨?_, fun v => ?_⟩
  · have := GlobalTheory.T.hermitian_quadratic_form_orbit_rational_vector_eq F E σ hCM _ _ J x a hS.2.2.1 gi
    rw [hgi] at this
    exact this
  · obtain ⟨g, hg⟩ := hy v
    have := GlobalTheory.T.hermitian_quadratic_form_orbit_rational_vector_eq F E σ hCM _ _ J x a hS.2.2.1 g
    rw [hg] at this
    exact this

end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
  {a : F} {B : Matrix (Fin (M + 1)) (Fin M) E} {J' : Matrix (Fin M) (Fin M) E}
  {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem inner_eq (hCM : IsCMExt F E σ) (hS : StepData σ J x a B J')
    {ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)}
    {mi' : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)}
    {mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)}
    (h : IsProd b ν' mi' mv') (hi : IsInvTup (Ainf F) σ J' mi') (hv : ∀ v, IsInvTup (Fv F v) σ J' (mv' v))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hg : ∀ v ∉ S, ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (g : HA (Fv F v) σ J),
        g • ratTup (F := F) (Fv F v) x = y → y ∈ latV b v →
        mv' v {y' | pairOf (Fv F v) σ J B y g y' ∈ latV b v} = mv' v (latV b v))
    (fi : (Fin 2 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (hfi : Measurable fi) (hfv : ∀ v, Measurable (fv v))
    {si : _} (hsi : IsSec (Ainf F) σ J x si)
    {sv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → HA (Fv F v) σ J}
    (hsv : ∀ v, IsSec (Fv F v) σ J x (sv v))
    (y : Fin 1 → Fin (M + 1) → AF F ⊗[F] E) (g : HA (AF F) σ J)
    (hy : g • ratTup (F := F) (AF F) x = y) :
    ∫⁻ y', {X : Fin 2 → Fin (M + 1) → AF F ⊗[F] E | ∀ v ∉ S, projV v (projFin X) ∈ latV b v}.indicator
        (fun X => fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X))) (pairOf (AF F) σ J B y g y') ∂ν' =
      {X : Fin 1 → Fin (M + 1) → AF F ⊗[F] E | ∀ v ∉ S, projV v (projFin X) ∈ latV b v}.indicator
        (fun X => (∫⁻ y', fi (pairOf (Ainf F) σ J B (projInf X) (si (projInf X)) y') ∂mi') *
          ∏ v ∈ S, ∫⁻ y', fv v (pairOf (Fv F v) σ J B (projV v (projFin X)) (sv v (projV v (projFin X))) y')
            ∂(mv' v)) y * tailProd b mv' S := by
  obtain ⟨gi, gv, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_local_components_adelic_unitary_element F E σ d b M J x B g
  rw [hy] at h1 h2
  by_cases hyL : y ∈ {X : Fin 1 → Fin (M + 1) → AF F ⊗[F] E | ∀ v ∉ S, projV v (projFin X) ∈ latV b v}
  · rw [Set.indicator_of_mem hyL]
    have hA : ∀ v, MeasurableSet {y' | pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) y' ∈ latV b v} :=
      fun v => measurable_pair (Fv F v) _ _ (measurableSet_latV b σ v 2 (M + 1))
    have key := isProd_sets b h S
      (fun v => {y' | pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) y' ∈ latV b v}) hA
      (by
        filter_upwards [GlobalTheory.T.eventually_integral_orthogonalComplement_pair F E σ d b M J x a B J' hS, h5, S.finite_toSet.compl_mem_cofinite]
          with v e1 e2 e3
        ext y'
        simp [e1 _ e2, hyL v e3])
      (fun v hv => hg v hv _ _ (h2 v).symm (hyL v hv))
      (fun y' => fi (pairOf (Ainf F) σ J B (projInf y) gi y'))
      (fun v y' => fv v (pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) y'))
      (hfi.comp (measurable_pair (Ainf F) _ _)) (fun v => (hfv v).comp (measurable_pair (Fv F v) _ _))
    rw [← GlobalTheory.T.lintegral_orthogonalComplement_pair_indep_groupElement F E σ hCM (Ainf F) M J x a B J' mi' hS hi (projInf y) gi _
      (h1.symm.trans (hsi _ ⟨gi, h1.symm⟩).symm) fi hfi,
      Finset.prod_congr rfl fun v _ => (GlobalTheory.T.lintegral_orthogonalComplement_pair_indep_groupElement F E σ hCM (Fv F v) M J x a B J' (mv' v) hS (hv v)
        (projV v (projFin y)) (gv v) _ ((h2 v).symm.trans (hsv v _ ⟨gv v, (h2 v).symm⟩).symm)
        (fv v) (hfv v)).symm, ← key, ← lintegral_indicator (measurableSet_cyl b S _ hA)]
    refine lintegral_congr fun y' => ?_
    by_cases hq : ∀ v ∉ S, pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) (projV v (projFin y')) ∈ latV b v
    · rw [Set.indicator_of_mem (by simpa only [Set.mem_setOf_eq, h4] using hq),
        Set.indicator_of_mem (by simpa only [Set.mem_setOf_eq] using hq)]
      simp only [h3, h4]
    · rw [Set.indicator_of_notMem (by simpa only [Set.mem_setOf_eq, h4] using hq),
        Set.indicator_of_notMem (by simpa only [Set.mem_setOf_eq] using hq)]
  · rw [Set.indicator_of_notMem hyL, zero_mul]
    refine (lintegral_congr fun y' => ?_).trans lintegral_zero
    refine Set.indicator_of_notMem (fun hm => hyL fun v hv => ?_) _
    have := hm v hv
    rw [h4] at this
    exact fst_mem b this

end

theorem twoStep_isProd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (ν : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (mi : Measure (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E)) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (mi' : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E)) (Ni : Measure (Fin 2 → Fin (M + 1) → Ainf F ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E)), StepData σ J x a B J' → IsProd b ν mi mv → IsProd b ν' mi' mv' → OnOrbit (Ainf F) σ J x mi → (∀ v, OnOrbit (Fv F v) σ J x (mv v)) → IsInvTup (Ainf F) σ J' mi' → (∀ v, IsInvTup (Fv F v) σ J' (mv' v)) → TwoStep (Ainf F) σ J x B mi mi' Ni → (∀ v, TwoStep (Fv F v) σ J x B (mv v) (mv' v) (Nv v)) → TwoStep (AF F) σ J x B ν ν' N → IsProd b N Ni Nv := by
  intro F E _ _ _ _ _ σ hCM d b M J x a B J' ν mi mv ν' mi' mv' N Ni Nv hS hν hν' hoi hov hii hiv
    hNi hNv hN
  have hfin := Filter.eventually_cofinite.1 (good_ae b hCM hS)
  have hg : ∀ v ∉ hfin.toFinset, ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (g : HA (Fv F v) σ J),
      g • ratTup (F := F) (Fv F v) x = y → y ∈ latV b v →
      mv' v {y' | pairOf (Fv F v) σ J B y g y' ∈ latV b v} = mv' v (latV b v) := by
    intro v hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
    exact hv _ (hiv v)
  obtain ⟨hsum, htail⟩ := GlobalTheory.T.tailProd_mul_of_lattice_mass_mul F E d b _ _ _ _ _ _ mi mv mi' mv' Nv hfin.toFinset hν.1 hν'.1
    (fun v hv => mass_mul b (hov v) (hNv v) (hg v hv))
  have hnice := nice_ainf_fv F
  refine isProd_of_large b σ N Ni Nv hfin.toFinset
    ⟨GlobalTheory.T.twoStep_pair_measure_finite_on_compacts F E σ hCM (Ainf F) hnice.1 M J x a B J' mi mi' Ni hS hoi hν.1.1 hν'.1.1 hii hNi,
     fun v => GlobalTheory.T.twoStep_pair_measure_finite_on_compacts F E σ hCM (Fv F v) (hnice.2 v) M J x a B J' (mv v) (mv' v) (Nv v) hS (hov v)
      (hν.1.2.1 v) (hν'.1.2.1 v) (hiv v) (hNv v), hsum⟩ fun S hSS fi fv hfi hfv => ?_
  obtain ⟨-, s, hs, -⟩ := exists_sec (σ := σ) (J := J) (B := B) (AF F) x
  obtain ⟨-, si, hsi, hsi'⟩ := exists_sec (σ := σ) (J := J) (B := B) (Ainf F) x
  choose sv hsv hsv' using fun v : HeightOneSpectrum (𝓞 F) =>
    (exists_sec (σ := σ) (J := J) (B := B) (Fv F v) x).2
  have hG := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b 2 (M + 1)
  have hG1 := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b 1 (M + 1)
  have hc2 := measurableSet_cyl b S _ fun v => measurableSet_latV b σ v 2 (M + 1)
  have hc1 := measurableSet_cyl b S _ fun v => measurableSet_latV b σ v 1 (M + 1)
  have hFi := hsi' mi' hν'.1.1 fi hfi
  have hFv := fun v => hsv' v (mv' v) (hν'.1.2.1 v) (fv v) (hfv v)
  have hm : Measurable fun X : Fin 2 → Fin (M + 1) → AF F ⊗[F] E =>
      fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) :=
    (hfi.comp hG.2.2.1.measurable).mul
      (Finset.measurable_prod _ fun v _ => (hfv v).comp (hG.2.2.2 v).measurable)
  rw [← lintegral_indicator hc2, hN _ (hm.indicator hc2) s hs, hNi fi hfi si hsi,
    Finset.prod_congr rfl fun v _ => hNv v (fv v) (hfv v) (sv v) (hsv v), htail S hSS, ← mul_assoc,
    ← hν.2 S _ _ hFi hFv, ← lintegral_indicator hc1, ← lintegral_mul_const' (tailProd b mv' S) _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [adelic_orbit b hCM hS hν hoi hov] with y hy
  exact inner_eq b hCM hS hν' hii hiv S (fun v hv => hg v fun h => hv (hSS h)) fi fv hfi hfv hsi hsv
    y (s y) (hs y hy)

end GlobalTheory.GaugeEx.TsProd
