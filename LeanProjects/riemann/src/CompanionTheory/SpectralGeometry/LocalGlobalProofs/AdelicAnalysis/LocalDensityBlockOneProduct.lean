import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneRightInjective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExistsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresInvariantStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneGramMeasurableSectionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneSumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageMeasure

theorem measurable_consTup {K : Type} [Zero K] [One K] [MeasurableSpace K] {M n : ℕ} :
    Measurable (consTup : (Fin n → Fin M → K) → Fin (n + 1) → Fin (M + 1) → K) := by
  refine measurable_pi_iff.2 fun a => ?_
  refine Fin.cases ?_ (fun a => ?_) a
  · exact measurable_const
  · refine measurable_pi_iff.2 fun i => ?_
    refine Fin.cases ?_ (fun i => ?_) i
    · exact measurable_const
    · exact (measurable_pi_apply i).comp (measurable_pi_apply a)

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gram_first (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (s : E) :
    gramR R σ (blockOne s J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
      fun _ _ => inclR R s := by
  funext a b
  simp only [gramR, hR, hform]
  rw [Fin.sum_univ_succ]
  simp [Fin.sum_univ_succ, JR, blockOne]

theorem inclR_algebraMap (R : Type) [CommRing R] [Algebra F R] (t : F) :
    inclR (F := F) (E := E) R (algebraMap F E t) = algebraMap F R t ⊗ₜ[F] (1 : E) := by
  show (1 : R) ⊗ₜ[F] (algebraMap F E t) = _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory.CompanionTheory.SW.StageMeasure

namespace GlobalTheory.CompanionTheory.SW

open GlobalTheory.CompanionTheory.SW.StageMeasure in
set_option maxHeartbeats 4000000 in

theorem fibre_block_stages : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFib R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∃ Ψ : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable Ψ ∧ (∀ h : HA R σ (blockOne (algebraMap F E t) J), Ψ (actW R σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT))) ∧ ∫⁻ X, φ X ∂(m (hermOf R σ _ hT')) = (c : ℝ≥0∞) ^ n * ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hTd hT' R _ _ _ _ _ hR d b lam hlam m m₁ m' hm hm₁ hm' c hc φ hφ
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
  obtain ⟨B, hBo, hTB, hBu, fib, hfib, hfibT⟩ := GlobalTheory.T.exists_fibre_family_block_one_eq_map_prod F E σ hCM M J hJ t ht n T hT hTd hT' R hR
    d b lam hlam m₁ m' hm₁ hm' c hc s hsm hs₁' hs₂'
  obtain ⟨h₁, h₂, h₃, h₄, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R (n + 1)
  obtain ⟨g, hgc, hg⟩ := hlift (M + 1) _ hJ'
  have hB₀ : IsOpen {S : HermR R σ (n + 1) | IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det} := by
    have hop : IsOpen {x : R ⊗[F] E | IsUnit x} := by
      have := (GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hCM R hR).isOpen_range
      convert this using 1
      ext x
      simp [IsUnit]
    exact hop.preimage (Continuous.matrix_det continuous_subtype_val)
  have hWn := hW (n + 1) (M + 1)
  have hHn := hH (n + 1)
  have hBn := hBorel (n + 1) (M + 1)
  have hU : {X | IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det} =
      g ⁻¹' {S : HermR R σ (n + 1) | IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det} := by
    ext X
    simp [hg X]
  have hU' : gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' B) = g ⁻¹' B := by
    ext X
    simp [hg X]
  have hm₀ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 1))
      (gramR R σ (blockOne (algebraMap F E t) J)) Subtype.val
      (g ⁻¹' {S : HermR R σ (n + 1) | IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det})
      (coordHerm R σ b lam (n + 1)) {S | IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det} m := by
    rw [← hU]
    exact hm
  rw [hU'] at hfib
  have hmT : fib (hermOf R σ _ hT') = m (hermOf R σ _ hT') :=
    GlobalTheory.T.fibre_family_eq_on_open_subset _ _ _ (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1))
      (gramR R σ (blockOne (algebraMap F E t) J)) g Subtype.val Subtype.val_injective hgc hg _ B hB₀ hBo hBu
      m fib hm₀ hfib _ hTB
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
  have hlf := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ R hR n _ _ m' (hW n M) (hH n) hm' (hermOf R σ T hT)).1
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
    have hinv := GlobalTheory.T.gram_fiber_measures_invariant F E σ hCM M J hJ R hR n _ _ m' (hW n M) (hH n) hm' u (hermOf R σ T hT)
    have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E => φ (actW R σ _ (s y) (consTup X)) :=
      hφ.comp (hact.comp ((measurable_const (a := s y)).prodMk measurable_consTup))
    calc ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂(m' (hermOf R σ T hT))
        = ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂((m' (hermOf R σ T hT)).map (actW R σ J u)) := by rw [hinv]
      _ = ∫⁻ X, φ (actW R σ _ (s y) (consTup (actW R σ J u X))) ∂(m' (hermOf R σ T hT)) :=
          lintegral_map hmeas (hactu u)
      _ = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT)) := by simp only [hX]
  · rw [← hmT, hfibT, lintegral_smul_measure, lintegral_map hφ hframe, lintegral_prod _ hF.aemeasurable]
    simp [ENNReal.smul_def]

end GlobalTheory.CompanionTheory.SW
