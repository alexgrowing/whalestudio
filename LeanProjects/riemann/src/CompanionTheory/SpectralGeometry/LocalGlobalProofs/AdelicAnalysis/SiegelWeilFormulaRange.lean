import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductRenormalizationStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZeroStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilOrbitalMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductLocalDensitiesConvergesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramMatrixLocalGlobalStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Fact

theorem exists_test_set {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (h : μ ≠ 0) :
    ∃ s, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ⊤ := by
  by_contra hcon
  push Not at hcon
  apply h
  apply Measure.measure_univ_eq_zero.mp
  rw [← iUnion_spanningSets μ]
  refine measure_iUnion_null fun i => ?_
  by_contra h0
  exact (measure_spanningSets_lt_top μ i).ne (hcon _ (measurableSet_spanningSets μ i) h0)

theorem fib_facts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b)
    (hdet : T.det ≠ 0) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hlam : lam.IsAddHaarMeasure) (mm : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hm : IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) mm) :
    SigmaFinite (mm (hermOf R σ T hT)) ∧
      (mm (hermOf R σ T hT) = 0 → ∀ X, gramR R σ J X ≠ T.map (inclR R)) := by
  have hR' := hR
  obtain ⟨h1, h2, h3, h4, -⟩ := hR'
  have hk := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hsc : SecondCountableTopology (R ⊗[F] E) := hk.2.2.1
  have hloc := GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ R hR n _ _ mm (hh.2.1 n M) (hh.2.2 n) hm
    (hermOf R σ T hT)
  obtain ⟨hlf, hpos⟩ := hloc
  refine ⟨inferInstance, fun h0 X hX => ?_⟩
  have hunit : IsUnit (gramR R σ J X).det := by
    rw [hX]
    have : (T.map (inclR R : E →+* R ⊗[F] E)).det = inclR R T.det :=
      (RingHom.map_det (inclR R : E →+* R ⊗[F] E) T).symm
    rw [this]
    exact (isUnit_iff_ne_zero.mpr hdet).map _
  exact hpos Set.univ isOpen_univ ⟨X, Set.mem_univ _, hX, hunit⟩ (by simp [h0])

theorem borel_tup {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hR : IsLocR R) (n M : ℕ) : BorelSpace (Fin n → Fin M → R ⊗[F] E) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hR
  exact (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R).2.2.2.2.2.2.2.1 n M

theorem pureL_insert {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) [DecidableEq (HeightOneSpectrum (𝓞 F))]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
    (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureL b (insert v S) φinf (Function.update φ v ((latV b v).indicator 1)) X = pureL b S φinf φ X := by
  have hprod : ∏ w ∈ S, (Function.update φ v ((latV b v).indicator 1)) w (projV w (projFin X)) =
      ∏ w ∈ S, φ w (projV w (projFin X)) :=
    Finset.prod_congr rfl fun w hw => by
      have hne : w ≠ v := fun h => hv (h ▸ hw)
      rw [Function.update_of_ne hne]
  have hmem : X ∈ intOff b S ↔
      X ∈ intOff b (insert v S) ∧ projV v (projFin X) ∈ latV b v := by
    constructor
    · intro h
      exact ⟨fun w hw => h w (fun hs => hw (Finset.mem_insert_of_mem hs)), h v hv⟩
    · rintro ⟨h1, h2⟩ w hw
      by_cases hwv : w = v
      · subst hwv; exact h2
      · exact h1 w (by simp [Finset.mem_insert, hwv, hw])
  unfold pureL
  by_cases h1 : X ∈ intOff b (insert v S)
  · by_cases h2 : projV v (projFin X) ∈ latV b v
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (hmem.2 ⟨h1, h2⟩), Finset.prod_insert hv,
        Function.update_self, hprod, Set.indicator_of_mem h2]
      simp
    · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem (fun h => h2 (hmem.1 h).2),
        Finset.prod_insert hv, Function.update_self, Set.indicator_of_notMem h2]
      simp
  · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun h => h1 (hmem.1 h).1)]

theorem exists_isEulerProd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) → ∀ I : Measure (Fin n → Fin M → AF F ⊗[F] E), IsLocallyFiniteMeasure I → (∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I) → I {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0 → ∃ c : ℝ≥0, IsEulerProd b I c (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn T hT hdet d b laminf lam hinf hlam minf hminf m hm I hIf hIinv hIsupp
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  have hFi := fib_facts σ hCM J hJ (Ainf F) hLi T hT hdet b laminf hinf.1 minf hminf
  have hFv : ∀ v, SigmaFinite (m v (hermOf (Fv F v) σ T hT)) ∧
      (m v (hermOf (Fv F v) σ T hT) = 0 →
        ∀ X, gramR (Fv F v) σ J X ≠ T.map (inclR (Fv F v))) := fun v => by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact fib_facts σ hCM J hJ (Fv F v) (hLv v) T hT hdet b (lam v) (hlam v).1 (m v) (hm v)
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.euler_product_local_densities_converges F E σ hCM M J hJ n hn T hT hdet d b lam hlam m hm
  by_cases h0 : minf (hermOf (Ainf F) σ T hT) = 0 ∨ ∃ v, m v (hermOf (Fv F v) σ T hT) = 0
  · have hempty : {X | gramR (AF F) σ J X = T.map (inclR (AF F))} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hX
      have hloc := (GlobalTheory.T.gram_matrix_local_global F E σ hCM M J hJ n X T).1.1 hX
      rcases h0 with h | ⟨v, h⟩
      · exact hFi.2 h _ hloc.1
      · exact (hFv v).2 h _ (hloc.2 v)
    rw [hempty, Set.compl_empty] at hIsupp
    rw [Measure.measure_univ_eq_zero.mp hIsupp]
    exact ⟨0, (GlobalTheory.T.euler_product_measure_zero F E σ hCM d b n M 0 0 _ _).2.2 hfin hsum h0⟩
  · push Not at h0
    obtain ⟨hinf0, hv0⟩ := h0
    choose c hc using GlobalTheory.T.siegel_weil_orbital_measure F E σ hCM M J hJ n T hT hdet d b laminf lam hinf hlam minf hminf m hm
      I hIf hIinv hIsupp
    obtain ⟨A, hAm, hA0, hAt⟩ := @exists_test_set _ _ (minf (hermOf (Ainf F) σ T hT)) hFi.1 hinf0
    choose B hBm hB0 hBt using fun v =>
      @exists_test_set _ _ (m v (hermOf (Fv F v) σ T hT)) (hFv v).1 (hv0 v)
    have hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∅ ⊆ S → ∀ v, v ∉ S →
        (c S : ℝ) = c (insert v S) * (m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal := by
      intro S _ v hv
      have hlatm : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
        haveI := borel_tup σ hCM (Fv F v) (hLv v) n M
        exact ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2.measurableSet
      let φ0 : ∀ w : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F w ⊗[F] E) → ℝ≥0∞ :=
        fun w => (B w).indicator 1
      let φ1 := Function.update φ0 v ((latV b v).indicator 1)
      have hφ0 : ∀ w, Measurable (φ0 w) := fun w => measurable_one.indicator (hBm w)
      have hφ1 : ∀ w, Measurable (φ1 w) := by
        intro w
        by_cases hw : w = v
        · subst hw
          simpa [φ1] using measurable_one.indicator hlatm
        · simpa [φ1, Function.update_of_ne hw] using hφ0 w
      have hAφ : Measurable (A.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hAm
      have e1 := hc S _ φ0 hAφ hφ0
      have e2 := hc (insert v S) _ φ1 hAφ hφ1
      have e3 : ∫⁻ X, pureL b (insert v S) (A.indicator 1) φ1 X ∂I =
          ∫⁻ X, pureL b S (A.indicator 1) φ0 X ∂I :=
        lintegral_congr fun X => pureL_insert b S v hv _ φ0 X
      rw [e3, e1, Finset.prod_insert hv] at e2
      have hp : ∏ w ∈ S, ∫⁻ X, φ1 w X ∂(m w (hermOf (Fv F w) σ T hT)) =
          ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(m w (hermOf (Fv F w) σ T hT)) :=
        Finset.prod_congr rfl fun w hw => by
          have hne : w ≠ v := fun h => hv (h ▸ hw)
          simp only [φ1, Function.update_of_ne hne]
      have hL : ∫⁻ X, φ1 v X ∂(m v (hermOf (Fv F v) σ T hT)) =
          m v (hermOf (Fv F v) σ T hT) (latV b v) := by
        simp only [φ1, Function.update_self]
        exact lintegral_indicator_one hlatm
      have hB : ∀ w, ∫⁻ X, φ0 w X ∂(m w (hermOf (Fv F w) σ T hT)) =
          m w (hermOf (Fv F w) σ T hT) (B w) := fun w => lintegral_indicator_one (hBm w)
      have hA : ∫⁻ X, A.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂(minf (hermOf (Ainf F) σ T hT)) =
          minf (hermOf (Ainf F) σ T hT) A := lintegral_indicator_one hAm
      rw [hp, hL, hA] at e2
      simp only [hB] at e2
      set Q := ∏ w ∈ S, m w (hermOf (Fv F w) σ T hT) (B w) with hQ
      set a := minf (hermOf (Ainf F) σ T hT) A with ha
      set L := m v (hermOf (Fv F v) σ T hT) (latV b v) with hLdef
      have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hB0 w
      have hQt : Q ≠ ⊤ := ENNReal.prod_ne_top fun w _ => hBt w
      have hP0 : a * Q ≠ 0 := mul_ne_zero hA0 hQ0
      have hPt : a * Q ≠ ⊤ := ENNReal.mul_ne_top hAt hQt
      have e4 : (c S : ℝ≥0∞) * (a * Q) = ((c (insert v S) : ℝ≥0∞) * L) * (a * Q) := by
        rw [e2]; ring
      have e5 := (ENNReal.mul_left_inj hP0 hPt).mp e4
      have e6 := congrArg ENNReal.toReal e5
      simpa [ENNReal.toReal_mul] using e6
    obtain ⟨c₀, S₀, -, hS₀⟩ := GlobalTheory.T.infinite_product_renormalization _ (fun v => (m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal) c ∅
      (fun _ => ENNReal.toReal_nonneg) hsum hstep
    refine ⟨c₀, hfin, hsum, S₀, fun S hS φinf φ hφi hφ => ?_⟩
    rw [hc S φinf φ hφi hφ]
    have hcS : (c S : ℝ≥0∞) = (c₀ : ℝ≥0∞) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := c S), (hS₀ S hS).2, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ENNReal.ofReal_coe_nnreal]
    rw [hcS]
    ring

end GlobalTheory.CompanionTheory.SW.Fact
