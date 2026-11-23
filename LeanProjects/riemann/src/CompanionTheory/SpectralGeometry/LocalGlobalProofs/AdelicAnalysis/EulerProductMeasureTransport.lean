import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjections
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosureProperties
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.EulerMove

theorem borel_ainf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := by
  obtain ⟨⟨-, scA, -⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have scA' : SecondCountableTopology (Ainf F × Af F) := scA
  haveI : SecondCountableTopology (Ainf F) :=
    (isEmbedding_prodMkLeft (0 : Af F)).secondCountableTopology
  haveI : T2Space (Ainf F) := GlobalTheory.CompanionTheory.AdeleTop.t2Space_infiniteAdeleRing_of_numberField_field F
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)).2.2.2.2.2.2.2.1 n M

theorem borel_af (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := by
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := lcA
  haveI := scA
  haveI := t2A
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)).2.2.2.2.2.2.2.1 n M

theorem borel_fv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.2.1 n M

theorem euler_move : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → IsEulerProd b I 1 minf m → IsEulerProd b (I.map e) 1 minf' m' := by
  intro F E _ _ _ _ _ σ hσ d b n M I minf minf' m m' e einf ev he heinf hev hcomm hgood cinf c hU
    hinf hloc hfin hE
  classical
  obtain ⟨-, hsum, S₀, hS₀⟩ := hE
  obtain ⟨hpi, hpf, hpv, hlat, hint, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b n M
  haveI := borel_af F E σ hσ n M
  haveI := borel_ainf F E σ hσ n M
  haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => borel_fv F E σ hσ n M v
  obtain ⟨S₁, hS₁⟩ := (GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F cinf cinf c c hU hU).2.2.2.2.2.2.2
  let S₂ : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hgood).toFinset
  have hS₂ : ∀ v, v ∉ S₂ → ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v := by
    intro v hv
    by_contra h
    exact hv (by simpa [S₂] using h)
  have hlatM : ∀ v, MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
    fun v => (hlat v).2.measurableSet
  have hcv : ∀ v, v ∉ S₁ ∪ S₂ → c v = 1 := fun v hv =>
    ((hS₁ (S₁ ∪ S₂) Finset.subset_union_left).1 v hv)
  have hmm : ∀ v, v ∉ S₁ ∪ S₂ → m' v (latV b v) = m v (latV b v) := by
    intro v hv
    have hv₂ : v ∉ S₂ := fun h => hv (Finset.mem_union_right _ h)
    have h1 := congrArg (fun μ => μ (latV b v)) (hloc v)
    simp only [Measure.map_apply (hev v) (hlatM v), hcv v hv, one_smul] at h1
    rw [← h1]
    congr 1
    ext X
    exact hS₂ v hv₂ X
  refine ⟨hfin, ?_, S₀ ∪ (S₁ ∪ S₂), ?_⟩
  · refine hsum.congr_cofinite ?_
    have hfinite : (↑(S₁ ∪ S₂) : Set (HeightOneSpectrum (𝓞 F))).Finite := Finset.finite_toSet (S₁ ∪ S₂)
    filter_upwards [hfinite.compl_mem_cofinite] with v hv
    rw [hmm v (by simpa using hv)]
  · intro S hS φinf φ hφinf hφ
    have hSS₀ : S₀ ⊆ S := Finset.union_subset_left hS
    have hSS₃ : S₁ ∪ S₂ ⊆ S := Finset.union_subset_right hS
    have hSS₁ : S₁ ⊆ S := Finset.union_subset_left hSS₃
    have hnot : ∀ v, v ∉ S → v ∉ S₁ ∪ S₂ := fun v hv h => hv (hSS₃ h)
    have hpm : Measurable (pureL b S φinf φ) := by
      refine Measurable.indicator ?_ (hint S).measurableSet
      refine (hφinf.comp hpi.measurable).mul ?_
      refine Finset.measurable_prod _ fun v _ => ?_
      exact (hφ v).comp ((hpv v).comp hpf).measurable
    have hmem : ∀ X, e X ∈ intOff b S ↔ X ∈ intOff b S := by
      intro X
      refine forall_congr' fun v => ?_
      refine imp_congr_right fun hv => ?_
      rw [(hcomm X).2 v]
      exact hS₂ v (fun h => hnot v hv (Finset.mem_union_right _ h)) _
    have hfun : (fun X => pureL b S φinf φ (e X)) =
        pureL b S (fun Y => φinf (einf Y)) (fun v Y => φ v (ev v Y)) := by
      funext X
      unfold pureL
      by_cases hX : X ∈ intOff b S
      · rw [Set.indicator_of_mem ((hmem X).2 hX), Set.indicator_of_mem hX, (hcomm X).1]
        congr 1
        exact Finset.prod_congr rfl fun v _ => by rw [(hcomm X).2 v]
      · rw [Set.indicator_of_notMem (fun h => hX ((hmem X).1 h)), Set.indicator_of_notMem hX]
    have hinfI : ∫⁻ Y, φinf (einf Y) ∂minf = (cinf : ℝ≥0∞) * ∫⁻ Y, φinf Y ∂minf' := by
      rw [← lintegral_map hφinf heinf, hinf, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    have hvI : ∀ v, ∫⁻ Y, φ v (ev v Y) ∂(m v) = (c v : ℝ≥0∞) * ∫⁻ Y, φ v Y ∂(m' v) := by
      intro v
      rw [← lintegral_map (hφ v) (hev v), hloc v, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    have hone : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by
      have := (hS₁ S hSS₁).2
      exact_mod_cast this
    have htail : (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) =
        ∏' v : {v // v ∉ S}, (m' v.1 (latV b v.1)).toReal :=
      tprod_congr fun v => by rw [hmm v.1 (hnot v.1 v.2)]
    rw [lintegral_map hpm he, hfun,
      hS₀ S hSS₀ (fun Y => φinf (einf Y)) (fun v Y => φ v (ev v Y)) (hφinf.comp heinf)
        (fun v => (hφ v).comp (hev v)), hinfI, htail]
    simp only [hvI]
    rw [Finset.prod_mul_distrib]
    congr 2
    calc (cinf : ℝ≥0∞) * (∫⁻ Y, φinf Y ∂minf') *
          ((∏ v ∈ S, (c v : ℝ≥0∞)) * ∏ v ∈ S, ∫⁻ Y, φ v Y ∂(m' v))
        = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) *
            ((∫⁻ Y, φinf Y ∂minf') * ∏ v ∈ S, ∫⁻ Y, φ v Y ∂(m' v)) := by ring
      _ = _ := by rw [hone, one_mul]

end GlobalTheory.CompanionTheory.SW.EulerMove
