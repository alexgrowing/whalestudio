import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilFormulaRange
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SummableOneDivAbsNormSq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlacesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalarStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.TnsIsTopologicalAddGroup
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.One

open PositivityTheory.Rg.Mass

theorem finite_rat_compact {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (n M : ℕ) (K : Set (Fin n → Fin M → AF F ⊗[F] E)) (hK : IsCompact K) :
    {X : Fin n → Fin M → E | ratTup (AF F) X ∈ K}.Finite := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  let f : (Fin n → Fin M → E) →+ (Fin n → Fin M → AF F ⊗[F] E) :=
    AddMonoidHom.mk' (ratTup (F := F) (AF F)) (fun X Y => by funext a i; simp [ratTup, map_add])
  have hdisc : DiscreteTopology f.range := Formalism.IndefR.Eqv.G5.tup_disc (F := F) (E := E) M n
  have hcl : IsClosed (f.range : Set (Fin n → Fin M → AF F ⊗[F] E)) := AddSubgroup.isClosed_of_discrete
  have hfin : (K ∩ (f.range : Set (Fin n → Fin M → AF F ⊗[F] E))).Finite :=
    (hK.inter_right hcl).finite ⟨DiscreteTopology.of_subset (s := (f.range : Set (Fin n → Fin M → AF F ⊗[F] E))) hdisc Set.inter_subset_right⟩
  refine (hfin.preimage hri.injOn).subset fun X hX => ⟨hX, X, rfl⟩

theorem theta_locFin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (hμ : IsHaarH F E σ M J μ) (h𝓕 : IsFDH F E σ M J μ 𝓕)
    (C : Set (HA (AF F) σ J)) (hC : IsCompact C) (hcov : ∀ h, ∃ γ : HFinIn (AF F) σ J, ∃ c ∈ C, h = γ • c)
    (hμ0 : μ 𝓕 ≠ 0) (hμt : μ 𝓕 ≠ ⊤) (n : ℕ) (S : Set (Fin n → Fin M → E)) :
    IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 S) := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, -⟩ := hact n
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  refine ⟨fun X₀ => ?_⟩
  obtain ⟨K, hK, hX⟩ := exists_compact_mem_nhds X₀
  have hK' : IsCompact ((fun p : HA (AF F) σ J × (Fin n → Fin M → AF F ⊗[F] E) => actW (AF F) σ J p.1 p.2) '' (C ×ˢ K)) :=
    (hC.prod hK).image ac
  have hP := finite_rat_compact σ hcm n M _ hK'
  set P := {X : Fin n → Fin M → E | ratTup (AF F) X ∈
    ((fun p : HA (AF F) σ J × (Fin n → Fin M → AF F ⊗[F] E) => actW (AF F) σ J p.1 p.2) '' (C ×ˢ K))} with hPdef
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have hcov' : ∀ h : HA (AF F) σ J, ∃ γ : Γ, ∃ c ∈ C, h = (γ : HA (AF F) σ J) * c := fun h => by
    obtain ⟨γ, c, hc, e⟩ := hcov h
    exact ⟨γ, c, hc, e⟩
  have hbound : ∀ h : HA (AF F) σ J, ∑' X : S, K.indicator (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
      (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ≤ (P.encard : ℝ≥0∞) := fun h => by
    obtain ⟨γ, c, hc, rfl⟩ := hcov' h
    choose t ht using fun X : Fin n → Fin M → E => PositivityTheory.PlacePermOperatorBicommutantSpan.act_rat (n := n) γ⁻¹ X
    have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X) = ratTup (AF F) (t X) := ht
    have hti : Function.Injective t := fun X Y e => by
      have h1 := congrArg (actW (AF F) σ J (γ : HA (AF F) σ J)) ((ht' X).trans ((congrArg (ratTup (AF F)) e).trans (ht' Y).symm))
      simp only [← a2, mul_inv_cancel, a1] at h1
      exact hri h1
    let A : Set S := {X | actW (AF F) σ J ((γ : HA (AF F) σ J) * c)⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E)) ∈ K}
    have e1 : ∑' X : S, K.indicator (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
        (actW (AF F) σ J ((γ : HA (AF F) σ J) * c)⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) = (A.encard : ℝ≥0∞) := by
      rw [← ENNReal.tsum_set_one, tsum_subtype A (fun _ => (1 : ℝ≥0∞))]
      refine tsum_congr fun X => ?_
      by_cases hx : X ∈ A
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show _ ∈ K from hx)]; rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show _ ∉ K from hx)]
    rw [e1]
    refine ENat.toENNReal_le.2 (Set.encard_le_encard_of_injOn (f := fun X : S => t X.1) ?_ ?_)
    · intro X hX
      refine ⟨(c, _), ⟨hc, hX⟩, ?_⟩
      change actW (AF F) σ J c (actW (AF F) σ J ((γ : HA (AF F) σ J) * c)⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) = ratTup (AF F) (t X.1)
      rw [← a2, mul_inv_rev, mul_inv_cancel_left, ht']
    · intro X _ Y _ e
      exact Subtype.ext (hti e)
  refine ⟨K, hX, ?_⟩
  have hm : Measurable (K.indicator (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)) :=
    measurable_one.indicator hK.measurableSet
  rw [← lintegral_indicator_one hK.measurableSet, PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 _ _ _ hm]
  have hle : ∫⁻ h in 𝓕, ∑' X : S, K.indicator (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
      (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ∂μ ≤ (P.encard : ℝ≥0∞) * μ 𝓕 := by
    refine (lintegral_mono hbound).trans ?_
    simp
  have hPt : (P.encard : ℝ≥0∞) ≠ ⊤ := by
    simpa using hP.encard_lt_top.ne
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hμ0))
    (lt_of_le_of_lt hle (ENNReal.mul_lt_top hPt.lt_top hμt.lt_top))

theorem euler_of_summable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ)
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (hinf : IsStdInf laminf) (hlam : ∀ v, IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v))
    (hfin : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤)
    (hsum : Summable fun v => |(m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1|)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hIf : IsLocallyFiniteMeasure I)
    (hIinv : ∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I)
    (hIsupp : I {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0) :
    ∃ c : ℝ≥0, IsEulerProd b I c (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)) := by
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  have hFi := GlobalTheory.CompanionTheory.SW.Fact.fib_facts σ hCM J hJ (Ainf F) hLi T hT hdet b laminf hinf.1 minf hminf
  have hFv : ∀ v, SigmaFinite (m v (hermOf (Fv F v) σ T hT)) ∧
      (m v (hermOf (Fv F v) σ T hT) = 0 →
        ∀ X, gramR (Fv F v) σ J X ≠ T.map (inclR (Fv F v))) := fun v => by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact GlobalTheory.CompanionTheory.SW.Fact.fib_facts σ hCM J hJ (Fv F v) (hLv v) T hT hdet b (lam v) (hlam v).1 (m v) (hm v)
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
    obtain ⟨A, hAm, hA0, hAt⟩ := @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ (minf (hermOf (Ainf F) σ T hT)) hFi.1 hinf0
    choose B hBm hB0 hBt using fun v =>
      @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ (m v (hermOf (Fv F v) σ T hT)) (hFv v).1 (hv0 v)
    have hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∅ ⊆ S → ∀ v, v ∉ S →
        (c S : ℝ) = c (insert v S) * (m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal := by
      intro S _ v hv
      have hlatm : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
        haveI := GlobalTheory.CompanionTheory.SW.Fact.borel_tup σ hCM (Fv F v) (hLv v) n M
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
        lintegral_congr fun X => GlobalTheory.CompanionTheory.SW.Fact.pureL_insert b S v hv _ φ0 X
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

theorem vector_length_formula_up_to_constant : CoCpt → LocMass → Prop1 := by
  intro hCo hLoc F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ
  obtain ⟨⟨C, hC, hcov⟩, hμ0, hμt⟩ := hCo F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm
  obtain ⟨C₁, hC₁⟩ := hLoc F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm
  have hE : algebraMap F E β ≠ 0 := fun h => hβ ((map_eq_zero _).1 h)
  let T : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E β
  have hT : ∀ a b, σ (T b a) = T a b := fun _ _ => σ.commutes β
  have hd : T.det ≠ 0 := by
    rw [Matrix.det_unique]
    exact hE
  obtain ⟨β', e, -, hh⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
  have hββ : β' = β := (algebraMap F E).injective (congrFun (congrFun e 0) 0).symm
  rw [hββ] at hh
  obtain ⟨t1, t2⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_inv F E σ hcm 2 J hJ μ 𝓕 hμ h𝓕 1 T
  have hlf : IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | gramE σ J X = T}) :=
    theta_locFin σ hcm 2 J hJ μ 𝓕 hμ h𝓕 C hC hcov hμ0 hμt 1 _
  have hfin : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤ := fun v => by
    have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
    obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
    haveI := hTR
    haveI := hLC
    haveI := hSC
    haveI := hT2
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have hh' := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b (lam v) (hlam v).1
    haveI hW := hh'.2.1 1 2
    haveI hH := hh'.2.2 1
    have hl := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 2 J hJ (Fv F v) hloc 1 _ _ (m v) hW hH (hm v)
      (hermOf (Fv F v) σ T hT)).1
    exact ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2).2.2.2.1 v).1.measure_lt_top
  have hsum : Summable fun v => |(m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| := by
    refine Summable.of_norm_bounded_eventually
      (g := fun v : HeightOneSpectrum (𝓞 F) => C₁ * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2))
      ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left C₁) ?_
    filter_upwards [hC₁, (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 β hβ] with v h1 h2
    have h3 := h1.2.2 _ h2
    rw [Real.norm_eq_abs, abs_abs, hh]
    simpa [div_eq_mul_inv] using h3
  obtain ⟨c, hc⟩ := euler_of_summable σ hcm 2 J hJ 1 T hT hd d b li lam hli hlam mi hmi m hm hfin hsum _ hlf t1 t2
  simp only [hh] at hc
  exact ⟨c, hc⟩

end GlobalTheory.CompanionTheory.Mass.One
