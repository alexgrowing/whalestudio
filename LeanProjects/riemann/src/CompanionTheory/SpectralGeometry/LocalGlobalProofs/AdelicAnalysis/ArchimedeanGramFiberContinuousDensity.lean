import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompacts
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityUnique
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsSizeMulLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresIntegralFormulaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianLocalContinuousCongruenceSectionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SizeFunctionRapidDecayIntegrableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LocGauss

theorem fibre_lintegral_eq_density {V X Y : Type}
    [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (B : Set X) (fib : X → Measure V)
    (hfib : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    (b₀ : X) (O : Set X) (hO : IsOpen O) (hOB : O ⊆ B) (hb₀ : b₀ ∈ O)
    (T : X → V → V) (κ : X → ℝ≥0)
    (hT : ContinuousOn (fun p : X × V => T p.1 p.2) (O ×ˢ Set.univ))
    (hκ : ContinuousOn κ O) (hκ0 : ∀ b ∈ O, κ b ≠ 0)
    (hm : ∀ b ∈ O, fib b = (κ b : ℝ≥0∞) • (fib b₀).map (T b))
    (w u : V → ℝ≥0∞) (hw : Measurable w) (hu : Continuous u) (hwμ : ∫⁻ v, w v ∂μ < ∞)
    (C : ℝ≥0) (huw : ∀ v, u v ≤ C * w v)
    (hwT : ∀ L : Set X, IsCompact L → L ⊆ O → ∃ c : ℝ≥0, ∀ b ∈ L, ∀ v,
      w (T b v) ≤ c * w v ∧ w v ≤ c * w (T b v))
    (d : X → ℝ≥0∞) (hd : ContinuousOn d O)
    (hdens : ∀ L : Set X, IsCompact L → L ⊆ O → ∫⁻ v in g ⁻¹' L, u v ∂μ = ∫⁻ b in L, d b ∂ν) :
    ∫⁻ v, u v ∂(fib b₀) = d b₀ := by
  have hum : Measurable u := hu.measurable
  have hAt : ∀ b ∈ O, ∀ v, ContinuousAt (fun p : X × V => T p.1 p.2) (b, v) := fun b hb v =>
    hT.continuousAt ((hO.prod isOpen_univ).mem_nhds ⟨hb, Set.mem_univ v⟩)
  have hTc : ∀ b ∈ O, Continuous (T b) := fun b hb =>
    continuous_iff_continuousAt.2 fun v =>
      ContinuousAt.comp (f := fun v : V => (b, v)) (g := fun p : X × V => T p.1 p.2)
        (hAt b hb v) (by fun_prop)
  have hTm : ∀ b ∈ O, Measurable (T b) := fun b hb => (hTc b hb).measurable

  have hint : ∀ b ∈ O, ∀ h : V → ℝ≥0∞, Measurable h →
      ∫⁻ v, h v ∂(fib b) = (κ b : ℝ≥0∞) * ∫⁻ v, h (T b v) ∂(fib b₀) := by
    intro b hb h hh
    rw [hm b hb, lintegral_smul_measure, lintegral_map hh (hTm b hb), smul_eq_mul]
  obtain ⟨L, hLn, hLO, hLc⟩ := local_compact_nhds (hO.mem_nhds hb₀)
  obtain ⟨c, hc⟩ := hwT L hLc hLO
  have hLB : L ⊆ B := hLO.trans hOB

  have hex : ∃ b₁ ∈ L, ∫⁻ v, w v ∂(fib b₁) < ∞ := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∫⁻ v in g ⁻¹' L, w v ∂μ = ∫⁻ b in L, ∫⁻ v, w v ∂(fib b) ∂ν :=
      FibreDensity.lintegral_preimage hι hf hg hfib hLc hLB hw
    have h2 : ∫⁻ b in L, ∫⁻ v, w v ∂(fib b) ∂ν = ∞ := by
      rw [setLIntegral_congr_fun hLc.measurableSet (g := fun _ => ∞)
        (fun b hb => top_le_iff.1 (hcon b hb)), setLIntegral_const,
        ENNReal.top_mul (Measure.measure_pos_of_mem_nhds ν hLn).ne']
    have h3 : ∫⁻ v in g ⁻¹' L, w v ∂μ ≤ ∫⁻ v, w v ∂μ := setLIntegral_le_lintegral _ _
    rw [h1, h2] at h3
    exact absurd (h3.trans_lt hwμ) (lt_irrefl _)
  obtain ⟨b₁, hb₁, hb₁f⟩ := hex

  have hI : ∫⁻ v, w v ∂(fib b₀) < ∞ := by
    have h1 := hint b₁ (hLO hb₁) w hw
    have hk : (κ b₁ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ0 b₁ (hLO hb₁)
    have h2 : ∫⁻ v, w (T b₁ v) ∂(fib b₀) < ∞ := by
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      rw [h1, hcon, ENNReal.mul_top hk] at hb₁f
      exact lt_irrefl _ hb₁f
    calc ∫⁻ v, w v ∂(fib b₀) ≤ ∫⁻ v, (c : ℝ≥0∞) * w (T b₁ v) ∂(fib b₀) :=
          lintegral_mono fun v => (hc b₁ hb₁ v).2
      _ = (c : ℝ≥0∞) * ∫⁻ v, w (T b₁ v) ∂(fib b₀) :=
          lintegral_const_mul _ (hw.comp (hTm b₁ (hLO hb₁)))
      _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top h2

  have hbound : ∀ b ∈ L, ∀ v, u (T b v) ≤ ((C : ℝ≥0∞) * c) * w v := by
    intro b hb v
    calc u (T b v) ≤ C * w (T b v) := huw _
      _ ≤ C * (c * w v) := by gcongr; exact (hc b hb v).1
      _ = _ := by rw [mul_assoc]
  have hbfin : ∫⁻ v, ((C : ℝ≥0∞) * c) * w v ∂(fib b₀) ≠ ∞ := by
    rw [lintegral_const_mul _ hw]
    exact (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top) hI).ne
  set H : X → ℝ≥0∞ := fun b => ∫⁻ v, u (T b v) ∂(fib b₀) with hH
  have hHfin : ∀ b ∈ L, H b ≠ ∞ := fun b hb =>
    ne_top_of_le_ne_top hbfin (lintegral_mono fun v => hbound b hb v)
  have hHc : ∀ b ∈ interior L, ContinuousAt H b := by
    intro b hb
    have hbL : L ∈ 𝓝 b := mem_interior_iff_mem_nhds.1 hb
    have hbO : b ∈ O := hLO (interior_subset hb)
    refine tendsto_lintegral_filter_of_dominated_convergence (fun v => ((C : ℝ≥0∞) * c) * w v)
      ?_ ?_ hbfin ?_
    · filter_upwards [hbL] with b' hb'
      exact hum.comp (hTm b' (hLO hb'))
    · filter_upwards [hbL] with b' hb'
      exact Filter.Eventually.of_forall fun v => hbound b' hb' v
    · refine Filter.Eventually.of_forall fun v => ?_
      have h1 : ContinuousAt (fun b' : X => T b' v) b :=
        ContinuousAt.comp (f := fun b' : X => (b', v)) (g := fun p : X × V => T p.1 p.2)
          (hAt b hbO v) (by fun_prop)
      exact (hu.continuousAt.comp h1).tendsto
  set G : X → ℝ≥0∞ := fun b => ∫⁻ v, u v ∂(fib b) with hG
  have hGc : ContinuousOn G (interior L) := by
    intro b hb
    have hbL : L ∈ 𝓝 b := mem_interior_iff_mem_nhds.1 hb
    have hbO : b ∈ O := hLO (interior_subset hb)
    have h1 : ContinuousAt (fun b' => (κ b' : ℝ≥0∞) * H b') b := by
      have hk : ContinuousAt (fun b' => (κ b' : ℝ≥0∞)) b :=
        ENNReal.continuous_coe.continuousAt.comp (hκ.continuousAt (hO.mem_nhds hbO))
      exact ENNReal.Tendsto.mul hk (Or.inr (hHfin b (interior_subset hb))) (hHc b hb)
        (Or.inr ENNReal.coe_ne_top)
    refine (h1.congr ?_).continuousWithinAt
    filter_upwards [hbL] with b' hb'
    exact (hint b' (hLO hb') u hum).symm
  have key := eq_of_setLIntegral_compact_eq X ν (interior L) isOpen_interior G d hGc
    (hd.mono (interior_subset.trans hLO)) (fun S hS hSL => ?_) b₀ (mem_interior_iff_mem_nhds.2 hLn)
  · exact key
  · have hSO : S ⊆ O := hSL.trans (interior_subset.trans hLO)
    rw [← hdens S hS hSO]
    exact (FibreDensity.lintegral_preimage hι hf hg hfib hS (hSO.trans hOB) hum).symm

end GlobalTheory.CompanionTheory.SW.LocGauss

namespace GlobalTheory.CompanionTheory.SW.LocGauss

theorem ofReal_inv_pow_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hab : a ≤ c * b)
    (N : ℕ) : ENNReal.ofReal ((b ^ N)⁻¹) ≤
      ((c ^ N).toNNReal : ℝ≥0∞) * ENNReal.ofReal ((a ^ N)⁻¹) := by
  have h1 : (b ^ N)⁻¹ ≤ c ^ N * (a ^ N)⁻¹ := by
    have h2 : a ^ N ≤ c ^ N * b ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ ha.le hab N
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  calc ENNReal.ofReal ((b ^ N)⁻¹) ≤ ENNReal.ofReal (c ^ N * (a ^ N)⁻¹) :=
        ENNReal.ofReal_le_ofReal h1
    _ = _ := ENNReal.ofReal_mul (by positivity)

set_option maxHeartbeats 400000 in

theorem fibre_rapid_eq_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J 1 μ ν m → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ D : HermR (Ainf F) σ 1 → ℝ, Continuous D → (∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (φ X) ∂μ = ∫⁻ S in U, ENNReal.ofReal (D S) ∂ν) → ∀ S : HermR (Ainf F) σ 1, IsUnit (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m S) = ENNReal.ofReal (D S) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b μ ν m hμ hν hfib φ hφc hφ0 hφr D hDc hD S hS
  have hLoc : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hLoc
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hKr, hKl, hKs, hK2, -, -, -, hVb, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI := hKr
  haveI := hKl
  haveI := hKs
  haveI := hK2
  haveI := hVb 1 M
  obtain ⟨hXl, hXs, hX2, hXb, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) 1
  haveI := hXl
  haveI := hXs
  haveI := hX2
  haveI := hXb
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  have hKU := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ (Ainf F) hLoc

  set B : Set (HermR (Ainf F) σ 1) :=
    {S | IsUnit (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det} with hBdef
  have hB : IsOpen B := by
    have hdet : Continuous fun S : HermR (Ainf F) σ 1 =>
        (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have : B = (fun S : HermR (Ainf F) σ 1 =>
        (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det) ⁻¹' Set.range Units.val := by
      ext S
      simp [hBdef, IsUnit]
    rw [this]
    exact hKU.isOpen_range.preimage hdet
  have hfib' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val (g ⁻¹' B) ν B m := by
    have e : g ⁻¹' B = {X | IsUnit (gramR (Ainf F) σ J X).det} := by
      ext X
      simp [hBdef, hgf]
    rw [e]
    exact hfib
  obtain ⟨B₁, s, hB₁, hSB₁, hsc, hs1, hsS⟩ := GlobalTheory.T.hermitian_local_continuous_congruence_section F E σ hσ (Ainf F) hLoc 1 S hS
  obtain ⟨κ, hκc, hκ0, -, hκ⟩ := GlobalTheory.T.gram_fiber_measures_gl_equivariant F E σ hσ M J hJ (Ainf F) hLoc 1 μ ν m hμ hν hfib
  obtain ⟨-, hsz0, N, hN⟩ := GlobalTheory.T.size_function_rapid_decay_integrable F E σ hσ d b 1 M μ hμ
  have hszc : Continuous (sizeTup b : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ) :=
    (GlobalTheory.T.size_function_rapid_decay_integrable F E σ hσ d b 1 M μ hμ).1
  obtain ⟨hg1, hg2, hg3, -, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Ainf F) 1
  set w : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞ :=
    fun X => ENNReal.ofReal (((1 + sizeTup b X) ^ N)⁻¹) with hw
  have hwm : Measurable w := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    refine Continuous.inv₀ ((continuous_const.add hszc).pow N) fun X => ?_
    have := hsz0 X
    positivity
  obtain ⟨C₀, hC₀⟩ := hφr N
  have huw : ∀ X, ENNReal.ofReal (φ X) ≤ (C₀.toNNReal : ℝ≥0∞) * w X := by
    intro X
    have h1 : 0 < (1 + sizeTup b X) ^ N := by
      have := hsz0 X
      positivity
    have h2 := hC₀ X
    rw [Complex.norm_real, Real.norm_of_nonneg (hφ0 X)] at h2
    have h3 : φ X ≤ C₀.toNNReal * ((1 + sizeTup b X) ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ h1]
      exact h2.trans (Real.le_coe_toNNReal _)
    calc ENNReal.ofReal (φ X) ≤ ENNReal.ofReal (C₀.toNNReal * ((1 + sizeTup b X) ^ N)⁻¹) :=
          ENNReal.ofReal_le_ofReal h3
      _ = _ := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have hrmulc : Continuous fun q : (Fin 1 → Fin M → Ainf F ⊗[F] E) ×
      Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E) => rmul (Ainf F) q.1 q.2 := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    refine continuous_finset_sum _ fun c _ => ?_
    refine Continuous.mul ?_ ?_
    · exact (continuous_apply i).comp ((continuous_apply c).comp continuous_fst)
    · exact continuous_snd.matrix_elem c a
  have hvalc : ContinuousOn (fun S' => ((s S' : GL (Fin 1) (Ainf F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E))) B₁ := Units.continuous_val.comp_continuousOn hsc
  have hinvc : ContinuousOn (fun S' => (((s S')⁻¹ : GL (Fin 1) (Ainf F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E))) B₁ :=
    Units.continuous_val.comp_continuousOn (continuous_inv.comp_continuousOn hsc)
  refine fibre_lintegral_eq_density μ ν (gramR (Ainf F) σ J) g Subtype.val Subtype.val_injective
    hgc hgf B m hfib' S (B₁ ∩ B) (hB₁.inter hB) Set.inter_subset_right ⟨hSB₁, hS⟩
    (fun S' X => rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E)))
    (fun S' => κ (s S')) ?_ ?_ ?_ ?_ w (fun X => ENNReal.ofReal (φ X)) hwm
    (ENNReal.continuous_ofReal.comp hφc) hN C₀.toNNReal huw ?_
    (fun S' => ENNReal.ofReal (D S')) (ENNReal.continuous_ofReal.comp hDc).continuousOn ?_
  · refine hrmulc.comp_continuousOn (continuous_snd.continuousOn.prodMk ?_)
    exact hvalc.comp (continuous_fst.continuousOn) fun p hp => hp.1.1
  · exact hκc.comp_continuousOn (hsc.mono Set.inter_subset_left)
  · exact fun S' _ => hκ0 _
  · exact fun S' hS' => hκ _ S S' (hsS S' hS'.1)
  · intro L hL hLO
    have hLB₁ : L ⊆ B₁ := hLO.trans Set.inter_subset_left
    have hC : IsCompact ((fun S' => ((s S' : GL (Fin 1) (Ainf F ⊗[F] E)) :
        Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E))) '' L ∪
        (fun S' => (((s S')⁻¹ : GL (Fin 1) (Ainf F ⊗[F] E)) :
        Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E))) '' L) :=
      (hL.image_of_continuousOn (hvalc.mono hLB₁)).union
        (hL.image_of_continuousOn (hinvc.mono hLB₁))
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.CompanionTheory.SW.SizeScale.size_rmul_le F E σ hσ d b 1 M _ hC
    have h1c : ∀ X Y : Fin 1 → Fin M → Ainf F ⊗[F] E, sizeTup b Y ≤ c * sizeTup b X →
        1 + sizeTup b Y ≤ max c 1 * (1 + sizeTup b X) := by
      intro X Y h
      have hX := hsz0 X
      have h1 : c ≤ max c 1 := le_max_left _ _
      have h2 : 1 ≤ max c 1 := le_max_right _ _
      nlinarith
    refine ⟨((max c 1) ^ N).toNNReal, fun S' hS' X => ?_⟩
    have hup := hc _ (Or.inl ⟨S', hS', rfl⟩) X
    have hdown := hc _ (Or.inr ⟨S', hS', rfl⟩)
      (rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E)))
    have hcancel : rmul (Ainf F) (rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E)))
        (((s S')⁻¹ : GL (Fin 1) (Ainf F ⊗[F] E)) : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) = X := by
      rw [hg2, ← Units.val_mul, mul_inv_cancel, Units.val_one, hg3]
    rw [hcancel] at hdown
    have p1 : 0 < 1 + sizeTup b X := by
      have := hsz0 X
      positivity
    have p2 : 0 < 1 + sizeTup b (rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E))) := by
      have := hsz0 (rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E)))
      positivity
    have hm0 : 0 ≤ max c 1 := hc0.le.trans (le_max_left _ _)
    exact ⟨ofReal_inv_pow_le p1 p2 hm0 (h1c _ _ hdown) N,
      ofReal_inv_pow_le p2 p1 hm0 (h1c _ _ hup) N⟩
  · intro L hL hLO
    have e : gramR (Ainf F) σ J ⁻¹' (Subtype.val '' L) = g ⁻¹' L := by
      ext X
      simp only [Set.mem_preimage, Set.mem_image, hgf]
      constructor
      · rintro ⟨x, hx, hxv⟩
        exact Subtype.val_injective hxv ▸ hx
      · exact fun hv => ⟨g X, hv, rfl⟩
    rw [← e]
    exact hD L hL.measurableSet

end GlobalTheory.CompanionTheory.SW.LocGauss
