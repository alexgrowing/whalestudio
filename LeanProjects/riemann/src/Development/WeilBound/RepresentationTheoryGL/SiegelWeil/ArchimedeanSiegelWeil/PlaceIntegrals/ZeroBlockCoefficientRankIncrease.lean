import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeZeroRankOneOfThreeLeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasures
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFibreMeasuresArchimedeanGramMapStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.GramMapFibreExistence
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TprodComplementSplitFinsetStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PureAdelicFunctionMeasurableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.ZeroBlockCoefficientInductionLeftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPlaneUnfoldingIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneEulerProductMeasureExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductMeasureCovolumeOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerVolumeAlmostAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicRankOneGlobalVolumeStatement
import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.ZeroBlockCoefficientInductionRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductLintegralLimitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ISupFiniteProductTailLimitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrameStatement

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem lintegral_iSup_places {ι Ω : Type} [Countable ι] [DecidableEq ι] [MeasurableSpace Ω]
    (I : Measure Ω) (S : Finset ι) (term : Finset ι → Ω → ℝ≥0∞) (hm : ∀ S', Measurable (term S'))
    (hmono : ∀ S' S'', S ⊆ S' → S' ⊆ S'' → ∀ y, term S' y ≤ term S'' y) (A : ℝ≥0∞)
    (c : Finset ι → ℝ≥0∞) (hint : ∀ S', S ⊆ S' → ∫⁻ y, term S' y ∂I = A * c S') :
    ∫⁻ y, (⨆ S', term (S ∪ S') y) ∂I = A * ⨆ S', c (S ∪ S') := by
  have hd : Directed (· ≤ ·) (fun S' : Finset ι => term (S ∪ S')) := by
    intro S₁ S₂
    refine ⟨S₁ ∪ S₂, fun y => ?_, fun y => ?_⟩
    · exact hmono _ _ Finset.subset_union_left
        (Finset.union_subset_union_right Finset.subset_union_left) y
    · exact hmono _ _ Finset.subset_union_left
        (Finset.union_subset_union_right Finset.subset_union_right) y
  rw [lintegral_iSup_directed (fun S' => (hm _).aemeasurable) hd, ENNReal.mul_iSup]
  exact iSup_congr fun S' => hint _ Finset.subset_union_left

theorem latV_measurable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
  exact (((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2).measurableSet

theorem fam_inf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)) (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ f, IsGramFibFree (Ainf F) σ J n (coordW (Ainf F) b lam n M) (coordHerm (Ainf F) σ b lam n) f := by
  have hB : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) _ b lam hlam
  exact GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap F E σ hCM M n J hJ _ _ (hW n M) (hH n)

theorem fam_fin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ f, IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) f := by
  have := PI.VolStabS.secondCountable_Fv F v
  have := PI.VolStabS.locallyCompact_Fv F v
  have hBv : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) _ b lam hlam
  exact PI.OmFibreUniq.W.gram_map_fibre_existence σ J v n hCM hJ _ _ (hW n M) (hH n)

theorem hyp_step : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (h₀ : ∀ a b : Fin n, σ ((0 : Matrix (Fin n) (Fin n) E) b a) = (0 : Matrix (Fin n) (Fin n) E) a b) (h₁ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) = (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b), (framesE σ J (0 : Matrix (Fin n) (Fin n) E)).Nonempty → SWFree σ J (0 : Matrix (Fin n) (Fin n) E) h₀ → SWFree σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁ := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn hnM h₀ h₁ hne hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  obtain ⟨hJ', he0⟩ := GlobalTheory.T.hyperbolic_sum_nondegenerate_frame F E σ hCM M J hJ
  have h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b :=
    fun a b => by simp
  obtain ⟨m₁inf, hm₁inf⟩ := fam_inf σ hCM (hypOne J) hJ' b laminf hinf.1 1
  obtain ⟨m'inf, hm'inf⟩ := fam_inf σ hCM J hJ b laminf hinf.1 n
  choose m₁ hm₁ using fun v => fam_fin σ hCM (hypOne J) hJ' b v (lam v) (hlam v).1 1
  choose m' hm' using fun v => fam_fin σ hCM J hJ b v (lam v) (hlam v).1 n
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := GlobalTheory.T.unitary_group_finite_volume F E σ hCM M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁
  have hE' := hSW d b laminf lam hinf hlam μ₁ 𝓕₁ hμ₁ h𝓕₁ m'inf m' hm'inf hm'
  have hE₁ := GlobalTheory.T.siegelWeilFree_zero_rank_one_of_three_le F E σ hCM (M + 2) (hypOne J) hJ' (by omega) h₂ ⟨_, he0⟩ d b laminf lam hinf hlam
    μ 𝓕 hμ h𝓕 m₁inf m₁ hm₁inf hm₁
  obtain ⟨hfinL, hsumL⟩ := GlobalTheory.T.zero_block_coefficient_induction_right F E σ hCM M J hJ n hn hnM h₀ h₁ h₂ d b lam hlam m m₁ m' hm hm₁ hm'
    hE₁.1 hE₁.2.1 hE'.1 hE'.2.1
  refine ⟨hfinL, hsumL, ?_⟩
  obtain ⟨dA, hdA, hdAE⟩ := GlobalTheory.T.covolume_one_euler_product_measure_exists F E σ hCM n d b laminf lam hinf hlam
  obtain ⟨hsumP, S₃, hS₃⟩ := GlobalTheory.T.hyperbolic_rank_one_global_volume F E σ hCM M J hJ (by omega) d b laminf lam hinf hlam h₂ m₁inf m₁
    hm₁inf hm₁ _ hE₁
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.euler_product_measure_covolume_one F E σ hCM M J hJ n d b laminf lam hinf hlam dA hdAE _ _ _ hE'
  have hStab := GlobalTheory.T.lattice_stabilizer_volume_almost_all F E σ hCM M J hJ n d b
  refine ⟨S₂ ∪ S₃ ∪ (Filter.eventually_cofinite.1 hStab).toFinset, fun S hS φinf φ hφinf hφ => ?_⟩
  have hS2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
  have hS3 : S₃ ⊆ S := fun x hx => hS (by simp [hx])
  have hS4 : ∀ v, v ∉ S → ∀ lam' : Measure (Fv F v), IsStdV v lam' →
      ∀ (m₀ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : HA (Fv F v) σ (hypOne J)),
      latStab σ (hypOne J) b v g → stageInt (Fv F v) σ J b lam' m₀ ((latV b v).indicator 1) g = m₀ (latV b v) := by
    intro v hv
    by_contra hc
    exact hv (hS (by simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inr hc))
  have hlatm : ∀ v, MeasurableSet (latV b v : Set (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    fun v => latV_measurable σ hCM b (n + 1) (M + 2) v
  have stg := GlobalTheory.T.zero_block_coefficient_induction_left F E σ hCM M J hJ n hn hnM h₀ h₁ h₂
  obtain ⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩ := stg (Ainf F) hLi d b laminf hinf.1 minf m₁inf m'inf hminf hm₁inf
    hm'inf φinf hφinf
  choose Ψ hΨm hΨ1 hΨ2 using fun v => stg (Fv F v) (hLv v) d b (lam v) (hlam v).1 (m v) (m₁ v) (m' v)
    (hm v) (hm₁ v) (hm' v) (φ v) (hφ v)
  choose G hGm hG1 hG2 using fun v => stg (Fv F v) (hLv v) d b (lam v) (hlam v).1 (m v) (m₁ v) (m' v)
    (hm v) (hm₁ v) (hm' v) ((latV b v).indicator 1) (measurable_one.indicator (hlatm v))

  obtain ⟨τ, hτ⟩ : ∃ τ : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, τ v = (m' v (hermOf (Fv F v) σ 0 h₀) (latV b v)).toReal :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : HeightOneSpectrum (𝓞 F) → ℝ,
      ∀ v, p v = (m₁ v (hermOf (Fv F v) σ 0 h₂) (primV σ J b v)).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨Mv, hMv⟩ : ∃ Mv : HeightOneSpectrum (𝓞 F) → ℝ,
      ∀ v, Mv v = (m v (hermOf (Fv F v) σ 0 h₁) (latV b v)).toReal := ⟨_, fun _ => rfl⟩
  have hτ' : ∀ v, m' v (hermOf (Fv F v) σ 0 h₀) (latV b v) = ENNReal.ofReal (τ v) := fun v => by
    rw [hτ, ENNReal.ofReal_toReal (hE'.1 v).ne]
  have hMv' : ∀ v, m v (hermOf (Fv F v) σ 0 h₁) (latV b v) = ENNReal.ofReal (Mv v) := fun v => by
    rw [hMv, ENNReal.ofReal_toReal (hfinL v).ne]
  have hτ0 : ∀ v, 0 ≤ τ v := fun v => by rw [hτ]; exact ENNReal.toReal_nonneg
  have hp0 : ∀ v, 0 ≤ p v := fun v => by rw [hp]; exact ENNReal.toReal_nonneg
  have hM0 : ∀ v, 0 ≤ Mv v := fun v => by rw [hMv]; exact ENNReal.toReal_nonneg
  have hsumτ : Summable fun v => |τ v - 1| := by simpa only [hτ] using hE'.2.1
  have hsump : Summable fun v => |p v - 1| := by simpa only [hp] using hsumP
  have hsumM : Summable fun v => |Mv v - 1| := by simpa only [hMv] using hsumL
  have hGprim : ∀ v, v ∉ S → ∀ y ∈ primV σ J b v, G v y = ENNReal.ofReal (τ v) := by
    rintro v hv _ ⟨g, hg, rfl⟩
    rw [hG1 v g, hS4 v hv (lam v) (hlam v) _ g hg, hτ']

  have hle : ∀ v, v ∉ S → τ v * p v ≤ Mv v := by
    intro v hv
    have h1 : ENNReal.ofReal (τ v) * m₁ v (hermOf (Fv F v) σ 0 h₂) (primV σ J b v) ≤
        m v (hermOf (Fv F v) σ 0 h₁) (latV b v) := by
      have e1 : m v (hermOf (Fv F v) σ 0 h₁) (latV b v) = ∫⁻ y, G v y ∂(m₁ v (hermOf (Fv F v) σ 0 h₂)) := by
        rw [← hG2 v, lintegral_indicator_one (hlatm v)]
      rw [e1]
      refine le_trans ?_ (mul_meas_ge_le_lintegral (hGm v) (ENNReal.ofReal (τ v)))
      gcongr
      intro y hy
      exact (hGprim v hv y hy).ge
    by_cases hpt : m₁ v (hermOf (Fv F v) σ 0 h₂) (primV σ J b v) = ⊤
    · rw [hp, hpt]
      simpa using hM0 v
    · have h2 : ENNReal.ofReal (τ v * p v) ≤ ENNReal.ofReal (Mv v) := by
        rw [ENNReal.ofReal_mul (hτ0 v), hp, ENNReal.ofReal_toReal hpt, ← hMv']
        exact h1
      exact (ENNReal.ofReal_le_ofReal_iff (hM0 v)).1 h2

  have hpure := hS₂ S hS2 φinf φ Ψinf Ψ G hφinf hφ hΨinf1 hΨ1 hG1
  obtain ⟨Ψ', hΨ'⟩ : ∃ Ψ' : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞,
      (fun v => if v ∈ S then Ψ v else G v) = Ψ' := ⟨_, rfl⟩
  rw [hΨ'] at hpure
  have hΨ'S : ∀ v, v ∈ S → Ψ' v = Ψ v := fun v hv => by rw [← hΨ']; simp [hv]
  have hΨ'N : ∀ v, v ∉ S → Ψ' v = G v := fun v hv => by rw [← hΨ']; simp [hv]
  have hΨ'm : ∀ v, Measurable (Ψ' v) := fun v => by
    by_cases hv : v ∈ S
    · rw [hΨ'S v hv]; exact hΨm v
    · rw [hΨ'N v hv]; exact hGm v
  have hpm : ∀ S', Measurable (purePr σ J b S' Ψinf Ψ') := fun S' =>
    GlobalTheory.T.euler_product_lintegral_limit F E σ hCM M J hJ d b S' Ψinf Ψ' hΨinfm hΨ'm
  obtain ⟨term, hterm⟩ : ∃ term : Finset (HeightOneSpectrum (𝓞 F)) → (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞,
      ∀ S' y, term S' y = ENNReal.ofReal (∏' v : {v // v ∉ S'}, τ v.1) * purePr σ J b S' Ψinf Ψ' y :=
    ⟨_, fun _ _ => rfl⟩
  have htm : ∀ S', Measurable (term S') := fun S' => by
    have e : term S' = fun y => ENNReal.ofReal (∏' v : {v // v ∉ S'}, τ v.1) * purePr σ J b S' Ψinf Ψ' y :=
      funext (hterm S')
    rw [e]
    exact (hpm S').const_mul _
  have hmono : ∀ S' S'', S ⊆ S' → S' ⊆ S'' → ∀ y, term S' y ≤ term S'' y := by
    intro S' S'' h1 h2 y
    rw [hterm, hterm]
    by_cases hy : ∀ v, v ∉ S' → projV v (projFin y) ∈ primV σ J b v
    · have hy2 : ∀ v, v ∉ S'' → projV v (projFin y) ∈ primV σ J b v := fun v hv => hy v fun h => hv (h2 h)
      have e1 : purePr σ J b S' Ψinf Ψ' y = Ψinf (projInf y) * ∏ v ∈ S', Ψ' v (projV v (projFin y)) :=
        Set.indicator_of_mem (s := {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E | ∀ v, v ∉ S' → projV v (projFin y) ∈ primV σ J b v}) hy _
      have e2 : purePr σ J b S'' Ψinf Ψ' y = Ψinf (projInf y) * ∏ v ∈ S'', Ψ' v (projV v (projFin y)) :=
        Set.indicator_of_mem (s := {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E | ∀ v, v ∉ S'' → projV v (projFin y) ∈ primV σ J b v}) hy2 _
      have e3 : ∏ v ∈ S'' \ S', Ψ' v (projV v (projFin y)) = ∏ v ∈ S'' \ S', ENNReal.ofReal (τ v) :=
        Finset.prod_congr rfl fun v hv => by
          have hvS' : v ∉ S' := (Finset.mem_sdiff.1 hv).2
          have hvS : v ∉ S := fun h => hvS' (h1 h)
          rw [hΨ'N v hvS, hGprim v hvS _ (hy v hvS')]
      have ht := GlobalTheory.T.tprod_complement_split_finset _ τ S' S'' hsumτ h2
      rw [e1, e2, ← Finset.prod_sdiff h2, e3, ht, ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => hτ0 v),
        ENNReal.ofReal_prod_of_nonneg fun v _ => hτ0 v]
      exact le_of_eq (by ring)
    · have e1 : purePr σ J b S' Ψinf Ψ' y = 0 :=
        Set.indicator_of_notMem (s := {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E | ∀ v, v ∉ S' → projV v (projFin y) ∈ primV σ J b v}) hy _
      rw [e1, mul_zero]
      exact bot_le
  have hτtail : ∀ S' : Finset (HeightOneSpectrum (𝓞 F)), 0 ≤ ∏' v : {v // v ∉ S'}, τ v.1 := fun S' =>
    (GlobalTheory.T.infinite_product_multipliable {v // v ∉ S'} (fun v => τ v.1) (hsumτ.subtype _)).2.2.2 fun _ => hτ0 _
  have hint : ∀ S', S ⊆ S' → ∫⁻ y, term S' y ∂(thetaMeas σ (hypOne J) μ 𝓕 (framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E))) =
      ((∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ 0 h₁))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ 0 h₁))) *
        ENNReal.ofReal ((∏ v ∈ S' \ S, Mv v) * ((∏' v : {v // v ∉ S'}, τ v.1) * ∏' v : {v // v ∉ S'}, p v.1)) := by
    intro S' hS'
    simp_rw [hterm]
    rw [lintegral_const_mul _ (hpm S'), hS₃ S' (hS3.trans hS') Ψinf Ψ' hΨinfm hΨ'm, ← hΨinf2]
    have hprod : ∏ v ∈ S', ∫⁻ y, Ψ' v y ∂(m₁ v (hermOf (Fv F v) σ 0 h₂)) =
        (∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ 0 h₁))) * ENNReal.ofReal (∏ v ∈ S' \ S, Mv v) := by
      rw [← Finset.prod_sdiff hS', mul_comm]
      congr 1
      · exact Finset.prod_congr rfl fun v hv => by rw [hΨ'S v hv, hΨ2 v]
      · rw [ENNReal.ofReal_prod_of_nonneg fun v _ => hM0 v]
        refine Finset.prod_congr rfl fun v hv => ?_
        rw [hΨ'N v (Finset.mem_sdiff.1 hv).2, ← hG2 v, lintegral_indicator_one (hlatm v), hMv']
    have hpt : ∏' v : {v // v ∉ S'}, (m₁ v.1 (hermOf (Fv F v.1) σ 0 h₂) (primV σ J b v.1)).toReal =
        ∏' v : {v // v ∉ S'}, p v.1 := tprod_congr fun v => (hp v.1).symm
    rw [hprod, hpt, ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => hM0 v), ENNReal.ofReal_mul (hτtail S')]
    ring
  have hcond : ∀ h : HA (AF F) σ (hypOne J), (⨆ S', term (S ∪ S') (actW (AF F) σ (hypOne J) h (e0 _ M))) =
      ∫⁻ Y, ∫⁻ a, pureL b S φinf φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA
        ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J (0 : Matrix (Fin n) (Fin n) E))) := by
    intro h
    obtain ⟨Sh, hSSh, hSh⟩ := hpure h
    have hv : ∀ S', Sh ⊆ S' → term S' (actW (AF F) σ (hypOne J) h (e0 _ M)) =
        ∫⁻ Y, ∫⁻ a, pureL b S φinf φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA
          ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J (0 : Matrix (Fin n) (Fin n) E))) := fun S' hS' => by
      rw [hterm, hSh S' hS']
      congr 2
      exact tprod_congr fun v => hτ v.1
    apply le_antisymm
    · refine iSup_le fun S' => ?_
      rw [← hv (S ∪ S' ∪ Sh) Finset.subset_union_right]
      exact hmono _ _ Finset.subset_union_left Finset.subset_union_left _
    · rw [← hv Sh subset_rfl]
      refine le_iSup_of_le Sh ?_
      rw [Finset.union_eq_right.2 hSSh]
  have hΦm := GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b (n + 1) (M + 2) S φinf φ hφinf hφ
  have hΨgm : Measurable fun y => ⨆ S', term (S ∪ S') y := Measurable.iSup fun S' => htm _
  have hB := GlobalTheory.T.hyperbolic_plane_unfolding_integral F E σ hCM M J hJ n hn hnM μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ dA hdA _ _ hΦm hΨgm hcond
  rw [hB, lintegral_iSup_places _ S term htm hmono _ _ hint,
    GlobalTheory.T.iSup_finite_product_tail_limit _ Mv τ p S hsumM hsumτ hsump hM0 hτ0 hp0 hle]
  simp only [ENNReal.coe_one, one_mul]
  congr 2
  exact tprod_congr fun v => hMv v.1

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep
