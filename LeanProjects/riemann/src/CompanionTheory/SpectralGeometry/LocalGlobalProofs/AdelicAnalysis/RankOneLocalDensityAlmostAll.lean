import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompacts
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresTransitivityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityBoundNonzeroStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EtaleAwayQuotientEqLocalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasurableCoordinateMapsTensorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlaces
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LocGood

theorem isOpen_ball_sub {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (s : Fv F v) : IsOpen {z : Fv F v | Valued.v (z - s) < Valued.v s} := by
  have h := Valued.isOpen_ball (Fv F v) (Valued.v.restrict s)
  have h' : IsOpen {y : Fv F v | Valued.v y < Valued.v s} := by
    simpa [Valuation.restrict_lt_iff] using h
  exact h'.preimage (continuous_id.sub continuous_const)

theorem local_mass {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (Bv : Matrix (Fin M × Fin d) (Fin M × Fin d) (Fv F v))
    (hform : ∀ x y : Fin M → Fv F v ⊗[F] E,
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J x y) =
        (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis (Fv F v) b).repr (x p.1) p.2) ⬝ᵥ
          (Bv *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis (Fv F v) b).repr (y p.1) p.2))
    (lam : Measure (Fv F v)) (hlam : IsStdV v lam)
    (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hm : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m)
    (s : Fv F v) (hs0 : s ≠ 0) (D : ℝ≥0)
    (hD : ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < Valued.v s} →
      (Measure.pi fun _ : Fin M × Fin d => lam)
        {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (Bv *ᵥ x)) ∈ A} =
        (D : ℝ≥0∞) * lam A) :
    (m (hermScal (Fv F v) σ s) (latV b v)).toReal = D := by
  classical
  have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v) := hloc.1
  haveI : LocallyCompactSpace (Fv F v) := hloc.2.1
  haveI : SecondCountableTopology (Fv F v) := hloc.2.2.1
  haveI : T2Space (Fv F v) := hloc.2.2.2.1
  haveI := hlam.1
  obtain ⟨-, -, -, hT2K, -, -, -, hBorW, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)
  haveI := hT2K
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b lam hlam.1
  obtain ⟨hLc, hLo, -, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b 1 M v
  obtain ⟨hSh, hSl, hSm⟩ := GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hCM (Fv F v) d b
  obtain ⟨-, -, -, hHB, hG⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Fv F v) 1
  obtain ⟨g, -, hgram⟩ := hG M J hJ
  obtain ⟨hcm, hcmap⟩ := GlobalTheory.T.measurable_coordinate_maps_tensor F E σ hCM (Fv F v) d b M lam hlam.1
  haveI : BorelSpace (Fin 1 → Fin M → Fv F v ⊗[F] E) := hBorW 1 M
  haveI : BorelSpace (HermR (Fv F v) σ 1) := hHB
  have hLm : MeasurableSet (latV (M := M) (n := 1) b v) := hLo.measurableSet
  obtain ⟨c, hcdef⟩ : ∃ c : (Fin 1 → Fin M → Fv F v ⊗[F] E) → (Fin M × Fin d → Fv F v),
      c = fun X p => (Algebra.TensorProduct.basis (Fv F v) b).repr (X 0 p.1) p.2 := ⟨_, rfl⟩
  rw [← hcdef] at hcm hcmap
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ,
      φ = (latV b v).indicator (fun _ => (1 : ℂ)) := ⟨_, rfl⟩
  have hcl : IsClopen (latV (M := M) (n := 1) b v) := ⟨hLc.isClosed, hLo⟩
  have hφc : Continuous φ := by
    rw [hφ]
    exact Continuous.indicator (fun a ha => by
      rw [hcl.frontier_eq] at ha; exact absurd ha (Set.notMem_empty a)) continuous_const
  have hφs : HasCompactSupport φ := by
    rw [hφ]
    exact HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨⟨hgc, hgi⟩, -⟩ := GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ hCM M J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm φ hφc hφs
  have hval : ∀ T, ∫ X, φ X ∂(m T) = (((m T (latV b v)).toReal : ℝ) : ℂ) := fun T => by
    rw [hφ, integral_indicator_const (1 : ℂ) hLm]
    simp [Measure.real]
  have hinj : Function.Injective (hermScal (Fv F v) σ) := hSh.injective
  have hEmb : MeasurableEmbedding (hermScal (Fv F v) σ) :=
    (hSh.homeomorph _).isClosedEmbedding.measurableEmbedding
  have hunit : ∀ z ∈ {z : Fv F v | Valued.v (z - s) < Valued.v s},
      hermScal (Fv F v) σ z ∈
        {S : HermR (Fv F v) σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)).det} := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
    have hu : IsUnit (algebraMap (Fv F v) (Fv F v ⊗[F] E) z) := (IsUnit.mk0 z hz0).map _
    show IsUnit (Matrix.det _)
    rw [Matrix.det_fin_one]
    simpa [hermScal, Algebra.TensorProduct.algebraMap_apply] using hu
  have hcont : ContinuousOn (fun z => (m (hermScal (Fv F v) σ z) (latV b v)).toReal)
      {z : Fv F v | Valued.v (z - s) < Valued.v s} := by
    have h1 := hgc.comp hSh.continuous.continuousOn hunit
    have h2 := Complex.continuous_re.comp_continuousOn h1
    refine h2.congr fun z _ => ?_
    simp [hval]
  have hkey : ∀ C : Set (Fv F v), IsCompact C → C ⊆ {z | Valued.v (z - s) < Valued.v s} →
      ∫ z in C, (m (hermScal (Fv F v) σ z) (latV b v)).toReal ∂lam = ((D : ℝ≥0∞) * lam C).toReal := by
    intro C hC hCB
    have hCm : MeasurableSet C := hC.measurableSet
    have hsub : hermScal (Fv F v) σ '' C ⊆
        {S : HermR (Fv F v) σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)).det} := by
      rintro _ ⟨z, hz, rfl⟩
      exact hunit z (hCB hz)
    have e : ∫ X in gramR (Fv F v) σ J ⁻¹' (Subtype.val '' (hermScal (Fv F v) σ '' C)), φ X
          ∂(coordW (Fv F v) b lam 1 M) =
        ∫ T in hermScal (Fv F v) σ '' C, ∫ X, φ X ∂(m T) ∂(coordHerm (Fv F v) σ b lam 1) :=
      hgi _ (hC.image hSh.continuous) hsub
    have hO : MeasurableSet (v.adicCompletionIntegers F : Set (Fv F v)) :=
      (Valued.isOpen_valuationSubring _).measurableSet
    have hTm : MeasurableSet {x : Fin M × Fin d → Fv F v |
        (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (Bv *ᵥ x)) ∈ C} := by
      have h1 : MeasurableSet {x : Fin M × Fin d → Fv F v |
          ∀ i, x i ∈ v.adicCompletionIntegers F} := by
        have : {x : Fin M × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
            ⋂ i, (fun x : Fin M × Fin d → Fv F v => x i) ⁻¹'
              (v.adicCompletionIntegers F : Set (Fv F v)) := by
          ext x; simp
        rw [this]
        exact MeasurableSet.iInter fun i => measurable_pi_apply i hO
      have hq : Continuous fun x : Fin M × Fin d → Fv F v =>
          (2 : Fv F v)⁻¹ * (x ⬝ᵥ (Bv *ᵥ x)) :=
        continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))
      exact h1.inter (hq.measurable hC.isClosed.measurableSet)
    have hset : (gramR (Fv F v) σ J ⁻¹' (Subtype.val '' (hermScal (Fv F v) σ '' C))) ∩ latV b v =
        c ⁻¹' {x : Fin M × Fin d → Fv F v |
          (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (Bv *ᵥ x)) ∈ C} := by
      ext X
      have hgX := hgram X
      have hQ : hermScal (Fv F v) σ ((2 : Fv F v)⁻¹ * (c X ⬝ᵥ (Bv *ᵥ c X))) = g X := by
        have h1 := hSl (g X)
        have h2 : ((g X : HermR (Fv F v) σ 1) : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) 0 0 =
            hR (Fv F v) σ J (X 0) (X 0) := by
          rw [← hgX]; rfl
        have h3 : algebraMap F (Fv F v) (1 / 2) = (2 : Fv F v)⁻¹ := by
          rw [one_div, map_inv₀, map_ofNat]
        rw [h2, hform, h3] at h1
        rw [hcdef]
        exact h1
      constructor
      · rintro ⟨⟨T, ⟨z, hz, rfl⟩, hT⟩, hL⟩
        refine ⟨fun p => ?_, ?_⟩
        · rw [hcdef]; exact hL 0 p.1 p.2
        · have h1 : hermScal (Fv F v) σ z = g X := Subtype.ext (hT.trans hgX)
          rw [← hinj (h1.trans hQ.symm)]
          exact hz
      · rintro ⟨hi, hq⟩
        refine ⟨⟨g X, ⟨_, hq, hQ⟩, hgX.symm⟩, fun a i k => ?_⟩
        obtain rfl : a = 0 := Subsingleton.elim _ _
        have := hi (i, k)
        rw [hcdef] at this
        exact this
    have hmass : coordW (Fv F v) b lam 1 M
        ((gramR (Fv F v) σ J ⁻¹' (Subtype.val '' (hermScal (Fv F v) σ '' C))) ∩ latV b v) =
        (D : ℝ≥0∞) * lam C := by
      rw [hset, ← Measure.map_apply hcm hTm, hcmap]
      exact hD C hCm hCB
    rw [hφ, setIntegral_indicator hLm, setIntegral_const, ← hφ, ← hSm lam hlam.1,
      hEmb.setIntegral_map, Set.preimage_image_eq _ hinj] at e
    simp_rw [hval] at e
    rw [integral_complex_ofReal, Measure.real, hmass, Complex.real_smul, mul_one] at e
    exact (Complex.ofReal_injective e).symm
  have hsmem : s ∈ {z : Fv F v | Valued.v (z - s) < Valued.v s} := by
    simpa [zero_lt_iff] using hs0
  have hfin := GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq (Fv F v) lam _ (isOpen_ball_sub v s)
    (fun z => ENNReal.ofReal (m (hermScal (Fv F v) σ z) (latV b v)).toReal)
    (fun _ => (D : ℝ≥0∞)) (ENNReal.continuous_ofReal.comp_continuousOn hcont) continuousOn_const
    (fun C hC hCB => by
      have hint : IntegrableOn (fun z => (m (hermScal (Fv F v) σ z) (latV b v)).toReal) C lam :=
        (hcont.mono hCB).integrableOn_compact hC
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg), hkey C hC hCB,
        ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hC.measure_lt_top.ne),
        setLIntegral_const])
    s hsmem
  have := congrArg ENNReal.toReal hfin
  simpa [ENNReal.toReal_ofReal ENNReal.toReal_nonneg] using this

theorem density_standard_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (lam : Measure (Fv F v)), IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 → |(m (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) := by
  intro F E _ _ _ _ _ σ hCM M J hJ h3 d b
  classical
  obtain ⟨B, hBs, hBd, hBt⟩ := GlobalTheory.CompanionTheory.SW.trace_form_coords F E σ hCM M J hJ d b
  obtain ⟨-, hun⟩ := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b
  have hd : d = 2 := by
    have h1 := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at h1
    exact h1.symm
  have hcard : Fintype.card (Fin M × Fin d) = 2 * M := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hd, mul_comm]
  have hent : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, algebraMap F (Fv F v) (B i j) ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases h0 : B i j = 0
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [h0, map_zero]
      exact zero_mem _
    · refine (hun _ h0).mono fun v hv => ?_
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hv.le
  filter_upwards [hun 2 two_ne_zero, hun _ hBd, hent] with v hv2 hvd hve lam hlam m hm s hs hs0
  have hv2' : Valued.v (2 : Fv F v) = 1 := by rwa [map_ofNat] at hv2
  have hdet : Valued.v (B.map (algebraMap F (Fv F v))).det = 1 := by
    have h1 := (algebraMap F (Fv F v)).map_det B
    rw [h1] at hvd
    exact hvd
  obtain ⟨D, hD1, hD⟩ := GlobalTheory.T.local_quadratic_density_bound_nonzero F v lam hlam hv2' (Fin M × Fin d)
    (B.map (algebraMap F (Fv F v))) (hBs.map _) (fun i j => hve i j) hdet M hcard h3 s hs hs0
  rw [local_mass σ hCM M J hJ d b v (B.map (algebraMap F (Fv F v))) (fun x y => hBt (Fv F v) x y)
    lam hlam m hm s hs0 D hD]
  exact hD1

end GlobalTheory.CompanionTheory.SW.LocGood
