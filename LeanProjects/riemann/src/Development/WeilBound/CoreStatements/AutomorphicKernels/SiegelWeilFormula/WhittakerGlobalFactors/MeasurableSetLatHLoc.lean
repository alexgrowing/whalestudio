import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MapRestrictIntH

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem measurableSet_latH_loc (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (latH σ b v n : Set (HermR (Fv F v) σ n)) := by
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hc := (GlobalTheory.CompanionTheory.SW.HermSd.hermVec_isHomeomorph hCM (Fv F v) b n).continuous
  have : (latH σ b v n : Set (HermR (Fv F v) σ n)) =
      (GlobalTheory.CompanionTheory.SW.HermSd.hermVec (Fv F v) σ b n) ⁻¹' (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
    Set.ext fun S => (HS.mem_latH_iff_vec σ b n v S).trans ⟨fun h i _ => h i, fun h i => h i (Set.mem_univ i)⟩
  rw [this]
  exact hc.measurable (MeasurableSet.univ_pi fun _ => hO.measurableSet)

theorem measurableSet_intHR (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSet (HS.intHR σ b n S) := by
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  have : HS.intHR σ b n S =
      ⋂ v, ⋂ (_ : v ∉ S), (HS.hV σ v) ⁻¹' (latH σ b v n : Set (HermR (Fv F v) σ n)) := by
    ext y
    simp only [HS.intHR, Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [this]
  refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => ?_
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  exact (HS.continuous_hermV σ hCM n v).measurable (measurableSet_latH_loc σ hCM b n v)

theorem herm_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (n d : ℕ)
    (bs : Module.Basis (Fin d) F E) (ν : Measure (HermR (AF F) σ n)) (hν : SdHerm F E σ (AF F) ψ n ν)
    (νi : Measure (HermR (Ainf F) σ n)) (hνi : SdHerm F E σ (Ainf F) (psiInf F ψ) n νi)
    (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n))
    (hνv : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      ∀ (gi : HermR (Ainf F) σ n → ℂ) (g : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ),
        (∀ v ∈ S, AEStronglyMeasurable (g v) (νv v)) →
        ∫ b in UH σ bs n S, gi (hermInf σ b) * ∏ v ∈ S, g v (hermV σ v (hermFin σ b)) ∂ν =
          (∫ x, gi x ∂νi) * ∏ v ∈ S, ∫ x, g v x ∂(νv v) := by
  classical
  obtain ⟨⟨laminf, hinf⟩, hlamE⟩ := GlobalTheory.T.exists_standard_local_measures F
  choose lam hlam using hlamE
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  obtain ⟨cinf, c, hU, hci, hcv⟩ := GlobalTheory.CompanionTheory.SW.sdHerm_eq_coord F E σ hCM d bs laminf lam hinf hlam ψ hψ n
  have eνi : νi = cinf • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ bs laminf n := (hci νi).1 hνi
  have eνv : ∀ v, νv v = c v • GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ bs (lam v) n := fun v => (hcv v (νv v)).1 (hνv v)
  have hfin : {v | ¬ c v = 1}.Finite := Filter.eventually_cofinite.1 hU.1
  refine ⟨hfin.toFinset, fun S hS gi g hg => ?_⟩
  have hprod : cinf * ∏ v ∈ S, c v = 1 := by
    have h2 := hU.2
    rwa [finprod_eq_prod_of_mulSupport_subset c (s := S) fun v hv => hS (hfin.mem_toFinset.2 hv)] at h2
  have hcS : ∀ v ∈ S, c v ≠ 0 := fun v hv h0 => by
    rw [Finset.prod_eq_zero hv h0, mul_zero] at hprod
    exact zero_ne_one hprod
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (HermR (Fv F v) σ n) := fun v => ⟨rfl⟩
  have hSF : ∀ v, SigmaFinite (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ bs (lam v) n) := fun v =>
    haveI : SigmaFinite (lam v) := Measure.IsAddHaarMeasure.sigmaFinite (lam v)
    HS.sigmaFinite_of_mp ((GlobalTheory.CompanionTheory.SW.HermSd.hermVec_isHomeomorph hCM (Fv F v) bs n).homeomorph _).toMeasurableEquiv
      (GlobalTheory.CompanionTheory.SW.HermSd.mp_hermVec hCM (Fv F v) bs n (lam v))
  haveI : ∀ v : S, SigmaFinite (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v.1) σ bs (lam v.1) n) := fun v => hSF v.1
  have hmp := HS.db_split σ hCM ψ hψ n ν hν bs laminf hinf lf hlf h1
  obtain ⟨-, -, -, -, -, -, -, -, hme0, -⟩ := GlobalTheory.T.hermitian_haar_splits_arch_times_finite F E σ hCM n ν hν.1
  have hme : MeasurableEmbedding (fun S : HermR (AF F) σ n => (HS.hInfR σ S, HS.hFinR σ S)) := hme0
  haveI : SFinite (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ bs laminf n) := by
    obtain ⟨hH, -⟩ := hinf
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
    have hmpI := GlobalTheory.CompanionTheory.SW.HermSd.mp_hermVec hCM (Ainf F) bs n laminf
    haveI : SigmaFinite laminf := Measure.IsAddHaarMeasure.sigmaFinite laminf
    haveI := HS.sigmaFinite_of_mp ((GlobalTheory.CompanionTheory.SW.HermSd.hermVec_isHomeomorph hCM (Ainf F) bs n).homeomorph _).toMeasurableEquiv hmpI
    infer_instance
  haveI : SFinite (GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n) := by
    obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
    haveI : BorelSpace (Af F) := ⟨rfl⟩
    have hmpF := GlobalTheory.CompanionTheory.SW.HermSd.mp_hermVec hCM (Af F) bs n lf
    haveI : SigmaFinite lf := Measure.IsAddHaarMeasure.sigmaFinite lf
    haveI := HS.sigmaFinite_of_mp ((GlobalTheory.CompanionTheory.SW.HermSd.hermVec_isHomeomorph hCM (Af F) bs n).homeomorph _).toMeasurableEquiv hmpF
    infer_instance

  set fS : HermR (Af F) σ n → ℂ := fun y => ∏ v ∈ S, g v (HS.hV σ v y) with hfS
  set Φ : HermR (Ainf F) σ n × HermR (Af F) σ n → ℂ :=
    fun p => gi p.1 * (HS.intHR σ bs n S).indicator fS p.2 with hΦ
  have e1 : ∫ b in UH σ bs n S, gi (HS.hInfR σ b) * ∏ v ∈ S, g v (HS.hV σ v (HS.hFinR σ b)) ∂ν =
      ∫ b, Φ (HS.hInfR σ b, HS.hFinR σ b) ∂ν := by
    rw [← integral_indicator (measurableSet_UH σ hCM bs n S)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    by_cases hb : b ∈ UH σ bs n S
    · have hb' : HS.hFinR σ b ∈ HS.intHR σ bs n S := hb
      rw [Set.indicator_of_mem hb]
      change _ = gi (HS.hInfR σ b) * (HS.intHR σ bs n S).indicator fS (HS.hFinR σ b)
      rw [Set.indicator_of_mem hb']
    · have hb' : HS.hFinR σ b ∉ HS.intHR σ bs n S := hb
      rw [Set.indicator_of_notMem hb]
      change _ = gi (HS.hInfR σ b) * (HS.intHR σ bs n S).indicator fS (HS.hFinR σ b)
      rw [Set.indicator_of_notMem hb', mul_zero]
  have e2 : ∫ b, Φ (HS.hInfR σ b, HS.hFinR σ b) ∂ν =
      (∫ x, gi x ∂GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ bs laminf n) *
        ∫ y, (HS.intHR σ bs n S).indicator fS y ∂GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n := by
    rw [hmp.integral_comp hme Φ]
    exact integral_prod_mul gi _
  have hAE : AEStronglyMeasurable (fun x : ∀ v : S, HermR (Fv F v.1) σ n => ∏ v : S, g v.1 (x v))
      (Measure.pi fun v : S => GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v.1) σ bs (lam v.1) n) := by
    have := Finset.aestronglyMeasurable_prod (μ := Measure.pi fun v : S => GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v.1) σ bs (lam v.1) n)
      (f := fun (v : S) (x : ∀ v : S, HermR (Fv F v.1) σ n) => g v.1 (x v)) Finset.univ (fun v _ => by
        have hgv : AEStronglyMeasurable (g v.1) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v.1) σ bs (lam v.1) n) := by
          have h0 := hg v.1 v.2
          rw [eνv v.1] at h0
          refine h0.mono_ac (fun s hs => ?_)
          rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at hs
          exact hs.resolve_left (by exact_mod_cast hcS v.1 v.2)
        exact hgv.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ v))
    convert this using 1
    funext x
    simp [Finset.prod_apply]
  have e3 : ∫ y, (HS.intHR σ bs n S).indicator fS y ∂GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n =
      ∏ v ∈ S, ∫ x, g v x ∂GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ bs (lam v) n := by
    rw [integral_indicator (measurableSet_intHR σ hCM bs n S)]
    have hρ : Measurable (fun y (v : S) => HS.hV σ v.1 y) :=
      measurable_pi_lambda _ fun v => (HS.continuous_hermV σ hCM n v.1).measurable
    have hmap := HS.map_restrict_intH σ hCM bs lam hlam lf hlf h1 n S
    have e4 : ∫ y in HS.intHR σ bs n S, fS y ∂GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n =
        ∫ x, ∏ v : S, g v.1 (x v) ∂((GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n).restrict (HS.intHR σ bs n S)).map
          (fun y (v : S) => HS.hV σ v.1 y) := by
      rw [integral_map hρ.aemeasurable (by rw [hmap]; exact hAE)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hfS]
      rw [← Finset.prod_coe_sort S]
    rw [e4, hmap, integral_fintype_prod_eq_prod (fun (v : S) => g v.1), ← Finset.prod_coe_sort S]
  show ∫ b in UH σ bs n S, gi (HS.hInfR σ b) * ∏ v ∈ S, g v (HS.hV σ v (HS.hFinR σ b)) ∂ν = _
  rw [e1, e2, e3, eνi, integral_smul_nnreal_measure]
  simp only [eνv, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]
  rw [Finset.prod_mul_distrib]
  have hprodC : ((cinf : ℝ) : ℂ) * ∏ v ∈ S, ((c v : ℝ) : ℂ) = 1 := by
    have := congrArg (fun x : NNReal => ((x : ℝ) : ℂ)) hprod
    push_cast at this
    exact this
  have key : ∀ (a k q p : ℂ), k * q = 1 → a * p = (k * a) * (q * p) := fun a k q p h => by
    linear_combination (-(a * p)) * h
  exact key _ _ _ _ hprodC

end PositivityTheory.SiegelWeilFormula.GFac

end
