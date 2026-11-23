import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilFormulaRange
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SummableOneDivAbsNormSq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlacesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalarStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cocompactness

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.Rank

open PositivityTheory.Rg.Base1 PositivityTheory.SiegelWeilFormula.Densx

theorem aniso_one {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J) : PositivityTheory.Rg.Mass.Aniso σ J := by
  intro x hx
  have hJ0 : J 0 0 ≠ 0 := by simpa [Matrix.det_unique] using hJ.2
  have h1 : σ (x 0) * J 0 0 * x 0 = 0 := by
    simpa [hE, hform, Matrix.mul_apply, dotProduct, Matrix.mulVec] using hx
  have hx0 : x 0 = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact (map_eq_zero σ).1 h
      · exact absurd h hJ0
    · exact h
  funext i
  rw [Subsingleton.elim i 0, hx0]; rfl

theorem coCpt_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (hμ : IsHaarH F E σ 1 J μ) (h𝓕 : IsFDH F E σ 1 J μ 𝓕) :
    (∃ C : Set (HA (AF F) σ J), IsCompact C ∧ ∀ h, ∃ γ : HFinIn (AF F) σ J, ∃ c ∈ C, h = γ • c) ∧ μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ := by
  have hA := aniso_one σ J hJ
  have hW : GlobalTheory.SiegelSet.IsWittFrame σ J (0 : Matrix (Fin 1) (Fin 0) E) 0 :=
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, fun z _ _ hz => hA z hz⟩
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.SiegelSet.Model.compact_quotient GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary hCM hJ hW
  refine ⟨⟨C, hC, fun h => ?_⟩, ?_, ?_⟩
  · obtain ⟨γ, hγ, c, hc, e⟩ := hcov h
    exact ⟨⟨γ, hγ⟩, c, hc, e⟩
  · exact (GlobalTheory.SiegelWeilConvCompare.measure_fundamentalDomain_pos F E σ 1 J μ hμ 𝓕 h𝓕).ne'
  · exact (((GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM 1 J hJ).2 μ hμ).2 𝓕 h𝓕).ne

theorem cfac_ne_zero {F : Type} (E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : cfac E v ≠ 0 := by
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    exact_mod_cast (by omega : 1 < Ideal.absNorm v.asIdeal)
  have he : eR E v ≤ 1 := by
    unfold eR PositivityTheory.SiegelWeilFormula.Gen.eSp
    split_ifs <;> norm_num
  have hpos : 0 < 1 - eR E v / (Ideal.absNorm v.asIdeal : ℝ) := by
    have : eR E v / (Ideal.absNorm v.asIdeal : ℝ) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    linarith
  unfold cfac
  simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
  exact inv_pos.2 hpos

theorem euler_of_factor {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (n M d : ℕ) (b : Module.Basis (Fin d) F E)
    (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mm : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hsi : SigmaFinite minf) (hsv : ∀ v, SigmaFinite (mm v)) (hinf0 : minf ≠ 0) (hv0 : ∀ v, mm v ≠ 0)
    (hfin : ∀ v, mm v (latV b v) < ⊤) (hsum : Summable fun v => |(mm v (latV b v)).toReal - 1|)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hc : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ℝ≥0, ∀ (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
      (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞),
      Measurable φinf → (∀ v, Measurable (φ v)) →
      ∫⁻ X, pureL b S φinf φ X ∂I = (c : ℝ≥0∞) * ((∫⁻ X, φinf X ∂minf) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(mm v))) :
    ∃ c : ℝ≥0, IsEulerProd b I c minf mm := by
  classical
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  choose c hc using hc
  obtain ⟨A, hAm, hA0, hAt⟩ := @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ minf hsi hinf0
  choose B hBm hB0 hBt using fun v => @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ (mm v) (hsv v) (hv0 v)
  have hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∅ ⊆ S → ∀ v, v ∉ S →
      (c S : ℝ) = c (insert v S) * (mm v (latV b v)).toReal := by
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
    have hp : ∏ w ∈ S, ∫⁻ X, φ1 w X ∂(mm w) = ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(mm w) :=
      Finset.prod_congr rfl fun w hw => by
        have hne : w ≠ v := fun h => hv (h ▸ hw)
        simp only [φ1, Function.update_of_ne hne]
    have hL : ∫⁻ X, φ1 v X ∂(mm v) = mm v (latV b v) := by
      simp only [φ1, Function.update_self]
      exact lintegral_indicator_one hlatm
    have hB : ∀ w, ∫⁻ X, φ0 w X ∂(mm w) = mm w (B w) := fun w => lintegral_indicator_one (hBm w)
    have hA : ∫⁻ X, A.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂minf = minf A :=
      lintegral_indicator_one hAm
    rw [hp, hL, hA] at e2
    simp only [hB] at e2
    set Q := ∏ w ∈ S, mm w (B w) with hQ
    set a := minf A with ha
    set L := mm v (latV b v) with hLdef
    have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hB0 w
    have hQt : Q ≠ ⊤ := ENNReal.prod_ne_top fun w _ => hBt w
    have hP0 : a * Q ≠ 0 := mul_ne_zero hA0 hQ0
    have hPt : a * Q ≠ ⊤ := ENNReal.mul_ne_top hAt hQt
    have e4 : (c S : ℝ≥0∞) * (a * Q) = ((c (insert v S) : ℝ≥0∞) * L) * (a * Q) := by
      rw [e2]; ring
    have e5 := (ENNReal.mul_left_inj hP0 hPt).mp e4
    have e6 := congrArg ENNReal.toReal e5
    simpa [ENNReal.toReal_mul] using e6
  obtain ⟨c₀, S₀, -, hS₀⟩ := GlobalTheory.T.infinite_product_renormalization _ (fun v => (mm v (latV b v)).toReal) c ∅
    (fun _ => ENNReal.toReal_nonneg) hsum hstep
  refine ⟨c₀, hfin, hsum, S₀, fun S hS φinf φ hφi hφ => ?_⟩
  rw [hc S φinf φ hφi hφ]
  have hcS : (c S : ℝ≥0∞) = (c₀ : ℝ≥0∞) *
      ENNReal.ofReal (∏' v : {v // v ∉ S}, (mm v.1 (latV b v.1)).toReal) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := c S), (hS₀ S hS).2, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
      ENNReal.ofReal_coe_nnreal]
  rw [hcS]
  ring

theorem euler_scaled {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ)
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (hinf : IsStdInf laminf) (hlam : ∀ v, IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v))
    (κ : HeightOneSpectrum (𝓞 F) → ℝ≥0) (hκ : ∀ v, κ v ≠ 0)
    (hfin : ∀ v, (κ v • m v (hermOf (Fv F v) σ T hT)) (latV b v) < ⊤)
    (hsum : Summable fun v => |((κ v • m v (hermOf (Fv F v) σ T hT)) (latV b v)).toReal - 1|)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hIf : IsLocallyFiniteMeasure I)
    (hIinv : ∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I)
    (hIsupp : I {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0) :
    ∃ c : ℝ≥0, IsEulerProd b I c (minf (hermOf (Ainf F) σ T hT)) (fun v => κ v • m v (hermOf (Fv F v) σ T hT)) := by
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
  have hzero : ∀ v, κ v • m v (hermOf (Fv F v) σ T hT) = 0 → m v (hermOf (Fv F v) σ T hT) = 0 := fun v h =>
    (smul_eq_zero.1 h).resolve_left (hκ v)
  by_cases h0 : minf (hermOf (Ainf F) σ T hT) = 0 ∨ ∃ v, κ v • m v (hermOf (Fv F v) σ T hT) = 0
  · have hempty : {X | gramR (AF F) σ J X = T.map (inclR (AF F))} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hX
      have hloc := (GlobalTheory.T.gram_matrix_local_global F E σ hCM M J hJ n X T).1.1 hX
      rcases h0 with h | ⟨v, h⟩
      · exact hFi.2 h _ hloc.1
      · exact (hFv v).2 (hzero v h) _ (hloc.2 v)
    rw [hempty, Set.compl_empty] at hIsupp
    rw [Measure.measure_univ_eq_zero.mp hIsupp]
    exact ⟨0, (GlobalTheory.T.euler_product_measure_zero F E σ hCM d b n M 0 0 _ _).2.2 hfin hsum h0⟩
  · push Not at h0
    obtain ⟨hinf0, hv0⟩ := h0
    have hsv : ∀ v, SigmaFinite (κ v • m v (hermOf (Fv F v) σ T hT)) := fun v => by
      haveI := (hFv v).1
      infer_instance
    refine euler_of_factor σ hCM n M d b _ _ hFi.1 hsv hinf0 hv0 hfin hsum I fun S => ?_
    obtain ⟨c, hc⟩ := GlobalTheory.T.siegel_weil_orbital_measure F E σ hCM M J hJ n T hT hdet d b laminf lam hinf hlam minf hminf m hm
      I hIf hIinv hIsupp S
    refine ⟨c / ∏ v ∈ S, κ v, fun φinf φ hφi hφ => ?_⟩
    rw [hc φinf φ hφi hφ]
    have hprod : ∏ v ∈ S, ∫⁻ X, φ v X ∂(κ v • m v (hermOf (Fv F v) σ T hT)) =
        ((∏ v ∈ S, κ v : ℝ≥0) : ℝ≥0∞) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ T hT)) := by
      rw [ENNReal.coe_finset_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    have hne : (∏ v ∈ S, κ v : ℝ≥0) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hκ v
    rw [hprod]
    have hcc : (c : ℝ≥0∞) = ((c / ∏ v ∈ S, κ v : ℝ≥0) : ℝ≥0∞) * ((∏ v ∈ S, κ v : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul, div_mul_cancel₀ _ hne]
    rw [hcc]
    ring

theorem mass_formula_of_total_mass_one : MassOne → Prop1 := by
  intro hMass F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β hβ
  obtain ⟨⟨C, hC, hcov⟩, hμ0, hμt⟩ := coCpt_one σ hcm J hJ μ 𝓕 hμ h𝓕
  have hE0 : algebraMap F E β ≠ 0 := fun h => hβ ((map_eq_zero _).1 h)
  let T : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E β
  have hT : ∀ a b, σ (T b a) = T a b := fun _ _ => σ.commutes β
  have hd : T.det ≠ 0 := by
    rw [Matrix.det_unique]
    exact hE0
  obtain ⟨β', e, -, hh⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
  have hββ : β' = β := (algebraMap F E).injective (congrFun (congrFun e 0) 0).symm
  rw [hββ] at hh
  obtain ⟨t1, t2⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_inv F E σ hcm 1 J hJ μ 𝓕 hμ h𝓕 1 T
  have hlf : IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 1 → E | gramE σ J X = T}) :=
    GlobalTheory.CompanionTheory.Mass.One.theta_locFin σ hcm 1 J hJ μ 𝓕 hμ h𝓕 C hC hcov hμ0 hμt 1 _
  have hfin0 : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤ := fun v => by
    have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
    obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
    haveI := hTR
    haveI := hLC
    haveI := hSC
    haveI := hT2
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have hh' := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b (lam v) (hlam v).1
    haveI hW := hh'.2.1 1 1
    haveI hH := hh'.2.2 1
    have hl := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 1 J hJ (Fv F v) hloc 1 _ _ (m v) hW hH (hm v)
      (hermOf (Fv F v) σ T hT)).1
    exact ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1).2.2.2.1 v).1.measure_lt_top
  have hfin : ∀ v, (cfac E v • m v (hermOf (Fv F v) σ T hT)) (latV b v) < ⊤ := fun v => by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hfin0 v)
  have hsum : Summable fun v => |((cfac E v • m v (hermOf (Fv F v) σ T hT)) (latV b v)).toReal - 1| := by
    have hev : ∀ᶠ v in Filter.cofinite,
        |((cfac E v • m v (hermOf (Fv F v) σ T hT)) (latV b v)).toReal - 1| = 0 := by
      filter_upwards [hMass F E σ hcm J hJ d b, (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 β hβ] with v h1 h2
      have h3 := h1 (lam v) (hlam v) (m v) (hm v) _ h2
      rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hh, h3]
      simp
    exact summable_of_finite_support (Filter.eventually_cofinite.1 hev)
  obtain ⟨c, hc⟩ := euler_scaled σ hcm 1 J hJ 1 T hT hd d b li lam hli hlam mi hmi m hm (cfac E) (cfac_ne_zero E)
    hfin hsum _ hlf t1 t2
  simp only [hh] at hc
  exact ⟨c, hc⟩

end GlobalTheory.CompanionTheory.Mass.Rank
