import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentExtendByUnitVectorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentUnitaryActionIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFreeSetProjectsCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralContinuousInParameterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureOrthogonalSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOneStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductUniqueness
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtensionStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.ContTwoF

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
open scoped TensorProduct ENNReal NNReal Matrix

theorem cont_double_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {X | LinearIndependent (R ⊗[F] E) X} → ContinuousOn (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Preal σ J t m₁ m' s φ z.1 z.2.1 z.2.2) ({α : R | IsUnit α} ×ˢ (Set.univ ×ˢ Set.univ)) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc hfree
  haveI iTR : IsTopologicalRing R := D.hR.1
  haveI iLC : LocallyCompactSpace R := D.hR.2.1
  haveI iSC : SecondCountableTopology R := D.hR.2.2.1
  haveI iT2 : T2Space R := D.hR.2.2.2.1
  have hval : IsOpenEmbedding (Units.val : Rˣ → R) := D.hR.2.2.2.2.2.2.1
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := kTR
  haveI := kLC
  haveI := kSC
  haveI := kT2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨eLC, eSC, eT2, eB, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R n
  haveI := eLC
  haveI := eSC
  haveI := eT2
  haveI := eB
  obtain ⟨gTG, gLC, gSC, gT2, gB, hactall⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  haveI := gTG
  haveI := gLC
  haveI := gSC
  haveI := gT2
  haveI := gB
  obtain ⟨hact, hact1, hactm, -⟩ := hactall (n + 1)
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ D.hCM R d b lam D.hlam
  haveI := hW n M
  haveI := hH n
  obtain ⟨-, -, hbd', -⟩ := GlobalTheory.T.local_fibre_measure_orthogonal_sum F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hloc₁, -, -, -, hgram₁⟩ :=
    GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := kB n M
  haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := kB 1 (M + 1)
  have hUo : IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    GlobalTheory.T.linearly_independent_frames_open F E σ D.hCM R D.hR n M

  have hCt : ∀ L : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact L →
      ∃ C : Set (Fin n → Fin M → R ⊗[F] E), IsCompact C ∧
        C ⊆ {X | LinearIndependent (R ⊗[F] E) X} ∧ ∀ h ∈ L, ∀ A c X,
        φ (actW R σ _ h (vec A c X)) ≠ 0 → X ∈ C := by
    intro L hL
    have hQc : IsCompact ((fun p : HA R σ (blockOne (algebraMap F E t) J) ×
        (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => actW R σ _ p.1⁻¹ p.2) '' (L ×ˢ tsupport φ)) := by
      refine (hL.prod hφc).image ?_
      exact hact.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd)
    have hQf : ∀ Y ∈ ((fun p : HA R σ (blockOne (algebraMap F E t) J) ×
        (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => actW R σ _ p.1⁻¹ p.2) '' (L ×ˢ tsupport φ)),
        LinearIndependent (R ⊗[F] E) Y := by
      rintro _ ⟨⟨h, z⟩, ⟨-, hz⟩, rfl⟩
      exact (GlobalTheory.T.linearIndependent_unitary_action_iff F E R σ (M + 1) (n + 1) _ h⁻¹ z).2 (hfree hz)
    obtain ⟨C, hC, hCf, hCv⟩ := GlobalTheory.T.compact_free_set_projects_compact (R ⊗[F] E) M n _ hQc hQf
    refine ⟨C, hC, hCf, fun h hh A c X hne => hCv A c X ?_⟩
    refine ⟨(h, actW R σ _ h (vec A c X)), ⟨hh, subset_tsupport _ hne⟩, ?_⟩
    simp only
    rw [← hactm, inv_mul_cancel, hact1]
  have cT := continuous_tmul_one (F := F) (E := E) R

  let G : (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E)) × HermR R σ n → ℝ :=
    fun q => ∫ X, φ (actW R σ _ q.1.1 (vec (q.1.2.1 ⊗ₜ[F] (1 : E)) q.1.2.2 X)) ∂(m' q.2)
  have hG : ∀ q, ContinuousAt G q := by
    intro q
    obtain ⟨L, hLc, hLn⟩ := exists_compact_mem_nhds q.1.1
    obtain ⟨C, hC, hCf, hCv⟩ := hCt L hLc
    have hWo : IsOpen (interior L ×ˢ (Set.univ : Set (R × (Fin n → R ⊗[F] E)))) :=
      isOpen_interior.prod isOpen_univ
    have hcΦ : Continuous (fun p : (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E)) ×
        (Fin n → Fin M → R ⊗[F] E) =>
        φ (actW R σ _ p.1.1 (vec (p.1.2.1 ⊗ₜ[F] (1 : E)) p.1.2.2 p.2))) := by
      refine hφ.comp (hact.comp ((continuous_fst.comp continuous_fst).prodMk ?_))
      exact continuous_vec.comp ((cT.comp (continuous_fst.comp (continuous_snd.comp continuous_fst))).prodMk
        ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd))
    have hj := GlobalTheory.T.fibre_integral_continuous_in_parameter (Fin n → Fin M → R ⊗[F] E) (HermR R σ n) _ (coordW R b lam n M)
      (coordHerm R σ b lam n) (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} hUo
      Set.univ isOpen_univ m' D.hm'
      (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E))
      (interior L ×ˢ Set.univ)
      (fun p X => φ (actW R σ _ p.1 (vec (p.2.1 ⊗ₜ[F] (1 : E)) p.2.2 X))) hcΦ.continuousOn hWo C hC hCf
      (by
        intro p hp v hv
        by_contra hne
        exact hv (hCv p.1 (interior_subset hp.1) _ _ _ hne))
    have hmem : ((interior L ×ˢ Set.univ) ×ˢ (Set.univ : Set (HermR R σ n))) ∈ 𝓝 q :=
      (hWo.prod isOpen_univ).mem_nhds ⟨⟨mem_interior_iff_mem_nhds.2 hLn, trivial⟩, trivial⟩
    exact hj.continuousAt hmem
  rintro ⟨α₀, c₀, S₀⟩ ⟨hα₀, -, -⟩
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨N, hNn, hNs, hNc⟩ := local_compact_nhds (hval.isOpen_range.mem_nhds hα₀)
  have hUc : IsCompact ((Units.val : Rˣ → R) ⁻¹' N) := by
    rw [hval.isInducing.isCompact_iff, Set.image_preimage_eq_of_subset hNs]
    exact hNc
  have hNi : IsCompact ((Units.val : Rˣ → R) '' ((Units.val : Rˣ → R) ⁻¹' N)⁻¹) :=
    hUc.inv.image Units.continuous_val
  obtain ⟨Dc, hDc, hDn⟩ := exists_compact_mem_nhds S₀
  let C₁ : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E) :=
    (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      scl (p.1 ⊗ₜ[F] (1 : E)) (fun _ : Fin 1 => p.2 0)) ''
        (((Units.val : Rˣ → R) '' ((Units.val : Rˣ → R) ⁻¹' N)⁻¹) ×ˢ tsupport φ)
  have hC₁c : IsCompact C₁ := by
    refine (hNi.prod hφc).image ?_
    refine continuous_pi fun _ => continuous_pi fun i => ?_
    have h1 : Continuous (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => p.2 0 i) :=
      (continuous_apply i).comp ((continuous_apply 0).comp continuous_snd)
    have h2 : Continuous (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => p.1 ⊗ₜ[F] (1 : E)) :=
      cT.comp continuous_fst
    exact h1.mul h2
  obtain ⟨C', hC'c, hC'⟩ := D.hcpt C₁ hC₁c
  obtain ⟨C₂, hC₂c, hC₂f, hC₂⟩ := hCt C' hC'c
  obtain ⟨cD, hcD⟩ := hbd' C₂ Dc hC₂c hC₂f hDc
  obtain ⟨Bd, hBd⟩ := hφ.bounded_above_of_compact_support hφc
  have hBd0 : 0 ≤ Bd := (norm_nonneg _).trans (hBd 0)
  haveI := hloc₁ (hermScal R σ (algebraMap F R t))
  have eD : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀), z.2.2 ∈ Dc :=
    (continuous_snd.comp continuous_snd).continuousAt hDn
  have eN : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀), z.1 ∈ N :=
    continuous_fst.continuousAt hNn
  have hmeas : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀),
      AEStronglyMeasurable (fun y₀ => G ((s y₀, z.1, z.2.1), z.2.2))
        (m₁ (hermScal R σ (algebraMap F R t))) := by
    refine Filter.Eventually.of_forall fun z => ?_
    have hc : Continuous (fun h : HA R σ (blockOne (algebraMap F E t) J) => G ((h, z.1, z.2.1), z.2.2)) := by
      refine continuous_iff_continuousAt.2 fun h => ?_
      refine ContinuousAt.comp (g := G) (f := fun h => ((h, z.1, z.2.1), z.2.2)) (hG _) ?_
      exact (((continuous_id.prodMk continuous_const)).prodMk continuous_const).continuousAt
    exact (hc.measurable.comp D.hs).aestronglyMeasurable
  have hcont : ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
      ContinuousAt (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => G ((s y₀, z.1, z.2.1), z.2.2))
        (α₀, c₀, S₀) := by
    refine Filter.Eventually.of_forall fun y₀ => ?_
    refine ContinuousAt.comp (g := G)
      (f := fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => ((s y₀, z.1, z.2.1), z.2.2)) (hG _) ?_
    exact ((continuous_const.prodMk (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd)).continuousAt
  have hbound : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀),
      ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
        ‖G ((s y₀, z.1, z.2.1), z.2.2)‖ ≤ C₁.indicator (fun _ => Bd * (cD : ℝ)) y₀ := by
    filter_upwards [eN, eD] with z hzN hzD
    filter_upwards [hgram₁ (hermScal R σ (algebraMap F R t))] with y₀ hy₀
    obtain ⟨u, hu⟩ := hNs hzN
    have hsec := D.hsec y₀ hy₀
    have hvan : ∀ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ≠ 0 → y₀ ∈ C₁ := by
      intro X hne
      refine ⟨(((u⁻¹ : Rˣ) : R), actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)),
        ⟨⟨u⁻¹, ?_, rfl⟩, subset_tsupport _ hne⟩, ?_⟩
      · simpa [Set.mem_inv, hu] using hzN
      · funext a i
        have ha : a = 0 := Subsingleton.elim _ _
        subst ha
        simp only [scl]
        rw [actW_vec_zero, hsec, ← hu, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv,
          mul_one, ← Algebra.TensorProduct.one_def, mul_one]
    by_cases hy : y₀ ∈ C₁
    · have h2 : s y₀ ∈ C' := hC' y₀ hy hy₀
      have hvanX : ∀ X, X ∉ C₂ → φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) = 0 :=
        fun X hX => by_contra fun hne => hX (hC₂ _ h2 _ _ _ hne)
      rw [Set.indicator_of_mem hy]
      change ‖∫ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ∂(m' z.2.2)‖ ≤ _
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvanX]
      have hfin : m' z.2.2 C₂ < ∞ := (hcD _ hzD).trans_lt ENNReal.coe_lt_top
      refine (norm_setIntegral_le_of_norm_le_const hfin (fun X _ => hBd _)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hBd0
      have := ENNReal.toReal_mono ENNReal.coe_ne_top (hcD _ hzD)
      simpa [Measure.real] using this
    · rw [Set.indicator_of_notMem hy]
      have h0 : (fun X => φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X))) = 0 :=
        funext fun X => by_contra fun hne => hy (hvan X hne)
      change ‖∫ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ∂(m' z.2.2)‖ ≤ _
      rw [h0]
      simp
  have hint : Integrable (C₁.indicator (fun _ => Bd * (cD : ℝ)))
      (m₁ (hermScal R σ (algebraMap F R t))) :=
    (integrable_indicator_iff hC₁c.isClosed.measurableSet).2 (integrableOn_const hC₁c.measure_lt_top.ne)
  exact continuousAt_of_dominated hmeas hbound hint hcont

end GlobalTheory.CompanionTheory.SW.StageF.ContTwoF
