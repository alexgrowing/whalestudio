import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationDisintegrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProperStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneGramMeasurableSectionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGramStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem compact_finite_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → (∀ C : Set (Fin n → Fin M → R ⊗[F] E), IsCompact C → m' (hermOf R σ T hT) C < ⊤) → ∀ C : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E), IsCompact C → m (hermOf R σ _ hT') C < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ t ht n T hT hT' R _ _ _ _ _ hR d b lam hlam m m₁ m' hm hm₁ hm' c hc hfin C hC
  obtain ⟨b1, b2, -⟩ := GlobalTheory.T.block_one_det_hermitian_gram F E σ hcm M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨b2 hJ.1, by rw [b1]; exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2⟩
  have hR' := hR
  obtain ⟨_, _, _, _, -⟩ := hR'
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have := hB n M
  have := hB 1 (M + 1)
  have := hB (n + 1) (M + 1)
  obtain ⟨hTG, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm _ _ hJ' R
  obtain ⟨-, k1, k2⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm R d b lam hlam
  have e0 : gramR R σ (blockOne (algebraMap F E t) J) (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    funext a a'
    simp only [gramR, hR, HeckeCharacterZeroLocus.SiegelWeilU.hR, hform, JR, blockOne, Fin.sum_univ_succ, hermScal, Fin.cons_zero, Fin.cons_succ,
      map_one, map_zero, one_mul, mul_one, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.map_apply,
      Matrix.of_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes t
  obtain ⟨s, sm, s1, s2⟩ := GlobalTheory.T.rank_one_gram_measurable_section F E σ hcm _ _ hJ' R hR (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) (by
    rw [e0, Matrix.det_unique]
    exact (ht.isUnit.map (algebraMap F R)).map (algebraMap R (R ⊗[F] E)))
  rw [e0] at s1 s2
  have hCm : MeasurableSet C := hC.measurableSet
  obtain ⟨Ψ, -, hΨ, hint⟩ := GlobalTheory.T.scalar_extension_fibre_measure F E σ hcm M J hJ t ht n T hT hT' R hR d b lam hlam m m₁ m' hm hm₁ hm' c hc
    (C.indicator 1) (measurable_one.indicator hCm)
  rw [lintegral_indicator_one hCm] at hint
  have hc' : Continuous (consTup : (Fin n → Fin M → R ⊗[F] E) → _) := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun i => ?_) i
    exacts [continuous_const, continuous_const, continuous_const, continuous_apply_apply a i]

  let p : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → (Fin 1 → Fin (M + 1) → R ⊗[F] E) := fun X _ => X 0
  have hpc : Continuous p := continuous_pi fun _ => continuous_apply 0
  have hC₁ : IsCompact (p '' C) := hC.image hpc
  obtain ⟨C', hC', hs⟩ := s2 _ hC₁

  let r : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) := fun Y a i => Y a.succ i.succ
  have hrc : Continuous r := continuous_pi fun a => continuous_pi fun i => continuous_apply_apply a.succ i.succ
  have hD : IsCompact ((fun q : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      actW R σ _ q.1⁻¹ q.2) '' (C' ×ˢ C)) :=
    (hC'.prod hC).image ((hact (n + 1)).1.comp (continuous_fst.inv.prodMk continuous_snd))
  obtain ⟨K, hK, hKsub⟩ : ∃ K : Set (Fin n → Fin M → R ⊗[F] E), IsCompact K ∧
      ∀ h ∈ C', ∀ X, actW R σ _ h (consTup X) ∈ C → X ∈ K := by
    refine ⟨_, hD.image hrc, fun h hh X hX => ⟨consTup X, ⟨(h, _), ⟨hh, hX⟩, ?_⟩, rfl⟩⟩
    show actW R σ _ h⁻¹ (actW R σ _ h (consTup X)) = consTup X
    rw [← (hact _).2.2.1, inv_mul_cancel, (hact _).2.1]
  have hKf := hfin K hK
  have hfirst : ∀ (h : HA R σ (blockOne (algebraMap F E t) J)) (X : Fin n → Fin M → R ⊗[F] E),
      p (actW R σ _ h (consTup X)) = actW R σ _ h (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) := fun h X => rfl
  have hae : ∀ᵐ y ∂(m₁ (hermScal R σ (algebraMap F R t))),
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    refine measure_mono_null ?_ (hm₁.1 (hermScal R σ (algebraMap F R t)))
    intro y hy hy'
    exact hy hy'.1
  have hbound : ∀ᵐ y ∂(m₁ (hermScal R σ (algebraMap F R t))),
      Ψ y ≤ (p '' C).indicator (fun _ => m' (hermOf R σ T hT) K) y := by
    filter_upwards [hae] with y hy
    have hy' := s1 y hy
    have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E => actW R σ _ (s y) (consTup X) :=
      ((hact _).1.comp (continuous_const.prodMk hc')).measurable
    have hΨy : Ψ y = m' (hermOf R σ T hT) {X | actW R σ _ (s y) (consTup X) ∈ C} := by
      have h1 := hΨ (s y)
      rw [hy'] at h1
      rw [h1]
      have h2 : (fun X : Fin n → Fin M → R ⊗[F] E =>
          C.indicator (1 : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (actW R σ _ (s y) (consTup X))) =
          {X | actW R σ _ (s y) (consTup X) ∈ C}.indicator 1 := by
        funext X
        simp [Set.indicator]
      rw [h2]
      exact lintegral_indicator_one (hmeas hCm)
    by_cases hyC : y ∈ p '' C
    · rw [Set.indicator_of_mem hyC, hΨy]
      exact measure_mono fun X hX => hKsub _ (hs y hyC hy) X hX
    · have hempty : {X | actW R σ _ (s y) (consTup X) ∈ C} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun X hX => hyC ⟨_, hX, ?_⟩
        rw [hfirst, hy']
      rw [hΨy, hempty, measure_empty]
      exact bot_le
  have hloc := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm _ _ hJ' R hR 1 _ _ _ (k1 1 (M + 1)) (k2 1) hm₁
    (hermScal R σ (algebraMap F R t))).1
  have hΨf : ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) < ⊤ := by
    refine (lintegral_mono_ae hbound).trans_lt ?_
    rw [lintegral_indicator_const hC₁.measurableSet]
    exact ENNReal.mul_lt_top hKf hC₁.measure_lt_top
  rw [hint]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hΨf

end GlobalTheory.CompanionTheory.WeilSiegel.Free
