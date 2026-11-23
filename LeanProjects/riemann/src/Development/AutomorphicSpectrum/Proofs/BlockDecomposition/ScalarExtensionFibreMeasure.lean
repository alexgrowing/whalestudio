import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationDisintegrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProperStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneProduct
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneRightInjective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneGramMeasurableSectionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeStage

theorem sigmaFinite_of_integrable {V : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] {U : Set V} (hU : IsOpen U)
    {μ : Measure V} (h0 : μ Uᶜ = 0)
    (hint : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U → Integrable φ μ) :
    SigmaFinite μ := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  have hfin : ∀ n, μ (Subtype.val '' K n) < ∞ := by
    intro n
    have hLc : IsCompact (Subtype.val '' K n) := (K.isCompact n).image continuous_subtype_val
    have hLU : Subtype.val '' K n ⊆ U := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    obtain ⟨f, hf1, hfc, hfs, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hLc hU hLU
    have hi := hint f f.continuous hfc hfs
    have hle : μ (Subtype.val '' K n) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
      calc μ (Subtype.val '' K n) = ∫⁻ x in Subtype.val '' K n, 1 ∂μ := by simp
        _ = ∫⁻ x in Subtype.val '' K n, ENNReal.ofReal (f x) ∂μ :=
            setLIntegral_congr_fun hLc.measurableSet fun x hx => by simp [hf1 hx]
        _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := setLIntegral_le_lintegral _ _
    exact hle.trans_lt hi.lintegral_lt_top
  refine ⟨⟨⟨fun n => Subtype.val '' K n ∪ Uᶜ, fun _ => Set.mem_univ _, fun n => ?_, ?_⟩⟩⟩
  · exact (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hfin n, by simp [h0]⟩)
  · refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ U
    · exact Set.mem_iUnion.2 ⟨K.find ⟨x, hx⟩, Or.inl ⟨⟨x, hx⟩, K.mem_find _, rfl⟩⟩
    · exact Set.mem_iUnion.2 ⟨0, Or.inr hx⟩

end GlobalTheory.CompanionTheory.WeilSiegel.FreeStage

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeStage

open GlobalTheory.CompanionTheory.SW.StageMeasure in
set_option maxHeartbeats 4000000 in

theorem fibre_block_stages_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∃ Ψ : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable Ψ ∧ (∀ h : HA R σ (blockOne (algebraMap F E t) J), Ψ (actW R σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT))) ∧ ∫⁻ X, φ X ∂(m (hermOf R σ _ hT')) = (c : ℝ≥0∞) ^ n * ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hT' R _ _ _ _ _ hR d b lam hlam m m₁ m' hm hm₁ hm' c hc φ hφ
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J hJ t ht
  obtain ⟨g₁, g₂, g₃, g₄, g₅, gAct⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) _ hJ' R
  obtain ⟨u₁, u₂, u₃, u₄, u₅, uAct⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ R
  have hgram : gramR R σ (blockOne (algebraMap F E t) J)
      (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    rw [gram_first, inclR_algebraMap]
    rfl
  have hunit : IsUnit (gramR R σ (blockOne (algebraMap F E t) J)
      (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E))).det := by
    rw [gram_first]
    have e := Matrix.det_fin_one (Matrix.of fun (_ _ : Fin 1) => inclR (F := F) R (algebraMap F E t))
    show IsUnit (Matrix.det (Matrix.of fun (_ _ : Fin 1) => inclR (F := F) R (algebraMap F E t)))
    rw [e]
    exact ((isUnit_iff_ne_zero.2 (by simpa using ht)).map (inclR (F := F) R))
  obtain ⟨s, hsm, hs₁, hs₂⟩ := GlobalTheory.T.rank_one_gram_measurable_section F E σ hCM (M + 1) _ hJ' R hR _ hunit
  have hs₁' := fun y (hy : gramR R σ (blockOne (algebraMap F E t) J) y =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1)) => hs₁ y (hy.trans hgram.symm)
  have hs₂' : ∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C →
      ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C,
        gramR R σ (blockOne (algebraMap F E t) J) y =
          (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C' := by
    intro C hC
    obtain ⟨C', hC', h⟩ := hs₂ C hC
    exact ⟨C', hC', fun y hy hg => h y hy (hg.trans hgram.symm)⟩
  obtain ⟨B, hBo, hTB, fib, hfib, hfibT⟩ := GlobalTheory.T.scalar_extension_fibre_formula F E σ hCM M J hJ t ht n T hT hT' R hR
    d b lam hlam m₁ m' hm₁ hm' c hc s hsm hs₁' hs₂'
  obtain ⟨h₁, h₂, h₃, h₄, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R (n + 1)
  obtain ⟨g, hgc, hg⟩ := hlift (M + 1) _ hJ'
  have hWn := hW (n + 1) (M + 1)
  have hHn := hH (n + 1)
  have hBn := hBorel (n + 1) (M + 1)
  have hU' : gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' B) = g ⁻¹' B := by
    ext X
    simp [hg X]
  have hfree := GlobalTheory.T.linearly_independent_frames_open F E σ hCM R hR (n + 1) (M + 1)
  have hm₀ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 1))
      (gramR R σ (blockOne (algebraMap F E t) J)) Subtype.val
      (g ⁻¹' Set.univ ∩ {X | LinearIndependent (R ⊗[F] E) X})
      (coordHerm R σ b lam (n + 1)) Set.univ m := by
    rw [Set.preimage_univ, Set.univ_inter]
    exact hm
  rw [hU'] at hfib
  have hmT : fib (hermOf R σ _ hT') = m (hermOf R σ _ hT') :=
    GlobalTheory.T.measurable_embedding_of_injective_proper _ _ _ (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1))
      (gramR R σ (blockOne (algebraMap F E t) J)) g Subtype.val Subtype.val_injective hgc hg _ hfree
      Set.univ B isOpen_univ hBo (Set.subset_univ _) m fib hm₀ hfib _ hTB
  have hBa := hBorel (n + 1) (M + 1)
  have hBb := hBorel n M
  have hBc := hBorel 1 (M + 1)
  have hact : Measurable fun p : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      actW R σ _ p.1 p.2 := (gAct (n + 1)).1.measurable
  have hactu : ∀ u : HA R σ J, Measurable (actW R σ J u : (Fin n → Fin M → R ⊗[F] E) → Fin n → Fin M → R ⊗[F] E) :=
    fun u => ((uAct n).1.comp (Continuous.prodMk_right u)).measurable
  have hframe : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      actW R σ _ (s p.1) (consTup p.2) :=
    hact.comp ((hsm.comp measurable_fst).prodMk (measurable_consTup.comp measurable_snd))
  have hF : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      φ (actW R σ _ (s p.1) (consTup p.2)) := hφ.comp hframe
  haveI hσ : SigmaFinite (m' (hermOf R σ T hT)) := by
    refine sigmaFinite_of_integrable (GlobalTheory.T.linearly_independent_frames_open F E σ hCM R hR n M) ?_ ?_
    · exact measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_right) (hm'.1 _)
    · intro f hfc hfs hft
      exact (hm'.2.2 f hfc hfs hft).1 _ (Set.mem_univ _)
  refine ⟨fun y => ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂(m' (hermOf R σ T hT)),
    hF.lintegral_prod_right', ?_, ?_⟩
  · intro h
    obtain ⟨ι, -, hιm, hιr, -, hιa⟩ := GlobalTheory.CompanionTheory.SW.StabFirst.stab_first F E σ hCM M J hJ t ht R
    have hy := hs₁' (actW R σ _ h (fun _ => Fin.cons 1 (fun _ => 0)))
      (((gAct 1).2.2.2 h _).trans hgram)
    set y := actW R σ _ h (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) with hydef
    have hfix : actW R σ _ ((s y)⁻¹ * h) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
        (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) := by
      calc actW R σ _ ((s y)⁻¹ * h) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E))
          = actW R σ _ (s y)⁻¹ y := (gAct 1).2.2.1 _ _ _
        _ = actW R σ _ (s y)⁻¹ (actW R σ _ (s y) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E))) := by
            rw [hy]
        _ = actW R σ _ ((s y)⁻¹ * s y) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) :=
            ((gAct 1).2.2.1 _ _ _).symm
        _ = _ := by rw [inv_mul_cancel, (gAct 1).2.1]
    obtain ⟨u, hu⟩ := (hιr _).2 hfix
    have hh : h = s y * ι u := by rw [hu, mul_inv_cancel_left]
    have hX : ∀ X : Fin n → Fin M → R ⊗[F] E,
        actW R σ _ h (consTup X) = actW R σ _ (s y) (consTup (actW R σ J u X)) := by
      intro X
      rw [hh, (gAct (n + 1)).2.2.1, hιa]
    have hinv := GlobalTheory.T.local_gram_fibration_disintegration F E σ hCM M J hJ R hR n _ _ m' (hW n M) (hH n) hm' u (hermOf R σ T hT)
    have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E => φ (actW R σ _ (s y) (consTup X)) :=
      hφ.comp (hact.comp ((measurable_const (a := s y)).prodMk measurable_consTup))
    calc ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂(m' (hermOf R σ T hT))
        = ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂((m' (hermOf R σ T hT)).map (actW R σ J u)) := by rw [hinv]
      _ = ∫⁻ X, φ (actW R σ _ (s y) (consTup (actW R σ J u X))) ∂(m' (hermOf R σ T hT)) :=
          lintegral_map hmeas (hactu u)
      _ = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT)) := by simp only [hX]
  · rw [← hmT, hfibT, lintegral_smul_measure, lintegral_map hφ hframe, lintegral_prod _ hF.aemeasurable]
    simp [ENNReal.smul_def]

end GlobalTheory.CompanionTheory.WeilSiegel.FreeStage
