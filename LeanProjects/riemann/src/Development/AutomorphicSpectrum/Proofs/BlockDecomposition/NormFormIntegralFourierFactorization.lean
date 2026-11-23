import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSquare

open GlobalTheory.CompanionTheory.WeilSB

section Main

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]
  [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

theorem square_identity (a : Fˣ) (u z : E) :
    (a : F) * Algebra.norm F u + Algebra.trace F E (conj F E u * z) =
      (a : F) * Algebra.norm F (u + algebraMap F E ((a : F)⁻¹) * z) + -(Algebra.norm F z) / a := by
  have ha : (a : F) ≠ 0 := a.ne_zero
  have h1 : Algebra.trace F E (conj F E u * z) = Algebra.trace F E (u * conj F E z) := by
    rw [← trace_conj (K := F) (conj F E u * z), map_mul, conj_conj]
  have h2 : u * conj F E (algebraMap F E ((a : F)⁻¹) * z) =
      algebraMap F E ((a : F)⁻¹) * (u * conj F E z) := by
    rw [map_mul, conj_algebraMap]
    ring
  rw [norm_add (K := F) u, h2, trace_algebraMap_mul, h1, map_mul (Algebra.norm F), norm_algebraMap_eq_sq]
  field_simp
  ring

theorem setIntegral_ball_add (μ : Measure E) [μ.IsAddHaarMeasure] (G : E → ℂ) {n : ℤ} {w : E}
    (hw : w ∈ valBall E n) :
    ∫ u in (valBall E n : Set E), G (u + w) ∂μ = ∫ u in (valBall E n : Set E), G u ∂μ := by
  have e : (valBall E n : Set E).indicator (fun u => G (u + w)) =
      fun u => (valBall E n : Set E).indicator G (u + w) := by
    funext u
    by_cases hu : u ∈ valBall E n
    · have hu' : u + w ∈ valBall E n := add_mem hu hw
      rw [Set.indicator_of_mem (show u ∈ (valBall E n : Set E) from hu),
        Set.indicator_of_mem (show u + w ∈ (valBall E n : Set E) from hu')]
    · have hu' : u + w ∉ valBall E n := fun h => hu (by simpa using sub_mem h hw)
      rw [Set.indicator_of_notMem (show u ∉ (valBall E n : Set E) from hu),
        Set.indicator_of_notMem (show u + w ∉ (valBall E n : Set E) from hu')]
  rw [← integral_indicator (measurableSet_valBall n), ← integral_indicator (measurableSet_valBall n), e]
  exact integral_add_right_eq_self _ w

theorem core_of_haar {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hcont : Continuous (algebraMap F E)) (μ : Measure E) [μ.IsAddHaarMeasure] (a : Fˣ)
    {Φ : E → ℂ} (hΦ : Φ ∈ SBE E) :
    ∃ n₀ : ℤ, ∀ n ≤ n₀,
      ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTs χ (conj F E) μ Φ u ∂μ =
        (∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂μ) *
          ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂μ := by
  have hN := continuous_norm_of (F := F) (E := E) hcont
  have hψ : Continuous (chE E χ) := continuous_traceChar hχ hχ1
  have hψ1 : chE E χ ≠ 1 := traceChar_ne_one hχ hχ1
  have hΦs : Φ ∈ schwartzBruhat E := ⟨hΦ.1, hΦ.2⟩
  have hFT : ∀ u, FTs χ (conj F E) μ Φ u = localFourier μ (chE E χ) Φ (conj F E u) := by
    intro u
    unfold FTs localFourier
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show Φ z * (χ (Algebra.trace F E (conj F E u * z)) : ℂ) =
      Φ z * (χ (Algebra.trace F E (z * conj F E u)) : ℂ)
    rw [mul_comm (conj F E u) z]
  obtain ⟨-, M₁, -, hM₁⟩ := exists_invariant_of_mem_schwartzBruhat
    (localFourier_mem_schwartzBruhat μ hψ hψ1 hΦs)
  obtain ⟨-, M₂, -, hM₂⟩ := exists_invariant_of_mem_schwartzBruhat hΦs
  have ha0 : algebraMap F E ((a : F)⁻¹) ≠ 0 := (map_ne_zero _).2 (inv_ne_zero a.ne_zero)
  have hai : algebraMap F E ((a : F)⁻¹) ∈ valBall E (ord (algebraMap F E ((a : F)⁻¹))) :=
    (mem_valBall_iff_le_ord ha0).2 le_rfl
  refine ⟨min M₁ (ord (algebraMap F E ((a : F)⁻¹)) + M₂), fun n hn => ?_⟩
  have hn₁ : n ≤ M₁ := hn.trans (min_le_left _ _)
  have hn₂ : n ≤ ord (algebraMap F E ((a : F)⁻¹)) + M₂ := hn.trans (min_le_right _ _)
  have hfin : IsFiniteMeasure (μ.restrict (valBall E n : Set E)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_valBall n).measure_lt_top⟩
  set G : E → ℂ := fun u => (χ ((a : F) * Algebra.norm F u) : ℂ) with hG
  set K : E → E → ℂ := fun u z => G u * (Φ z * (χ (Algebra.trace F E (conj F E u * z)) : ℂ)) with hK
  have hint : Integrable (Function.uncurry K) ((μ.restrict (valBall E n : Set E)).prod μ) := by
    have hΦi : Integrable Φ μ := integrable_of_mem_schwartzBruhat μ hΦs
    have hp := (integrable_const (μ := μ.restrict (valBall E n : Set E)) (1 : ℂ)).mul_prod hΦi
    have hc : Continuous fun p : E × E => (χ ((a : F) * Algebra.norm F p.1) : ℂ) *
        (chE E χ (conj F E p.1 * p.2) : ℂ) :=
      ((continuous_subtype_val.comp hχ).comp (continuous_const.mul (hN.comp continuous_fst))).mul
        ((continuous_subtype_val.comp hψ).comp
          ((continuous_conj.comp continuous_fst).mul continuous_snd))
    have hb := hp.bdd_mul (c := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      rw [norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul])
    refine hb.congr (Filter.Eventually.of_forall fun p => ?_)
    show _ = G p.1 * (Φ p.2 * (χ (Algebra.trace F E (conj F E p.1 * p.2)) : ℂ))
    show (χ ((a : F) * Algebra.norm F p.1) : ℂ) * (χ (Algebra.trace F E (conj F E p.1 * p.2)) : ℂ) *
      (1 * Φ p.2) = _
    simp only [hG]
    ring
  have hinner : ∀ z, ∫ u in (valBall E n : Set E), K u z ∂μ =
      (∫ u in (valBall E n : Set E), G u ∂μ) * ((χ (-(Algebra.norm F z) / a) : ℂ) * Φ z) := by
    intro z
    by_cases hz : Φ z = 0
    · simp [hK, hz]
    have hw : algebraMap F E ((a : F)⁻¹) * z ∈ valBall E n :=
      valBall_antitone hn₂ (mul_mem_valBall hai (hM₂ z hz))
    have e : ∀ u, K u z = ((χ (-(Algebra.norm F z) / a) : ℂ) * Φ z) *
        G (u + algebraMap F E ((a : F)⁻¹) * z) := by
      intro u
      have h := congrArg (fun t => (χ t : ℂ)) (square_identity a u z)
      simp only [AddChar.map_add_eq_mul, Circle.coe_mul] at h
      simp only [hK, hG]
      linear_combination Φ z * h
    simp only [e]
    rw [integral_const_mul, setIntegral_ball_add μ G hw]
    ring
  calc ∫ u, G u * FTs χ (conj F E) μ Φ u ∂μ
      = ∫ u in (valBall E n : Set E), G u * FTs χ (conj F E) μ Φ u ∂μ := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
        have : localFourier μ (chE E χ) Φ (conj F E u) = 0 := by
          by_contra h
          exact hu (conj_mem_valBall_iff.1 (valBall_antitone hn₁ (hM₁ _ h)))
        rw [hFT, this, mul_zero]
    _ = ∫ u in (valBall E n : Set E), ∫ z, K u z ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show G u * FTs χ (conj F E) μ Φ u = ∫ z, K u z ∂μ
        simp only [hK]
        rw [integral_const_mul]
        rfl
    _ = ∫ z, ∫ u in (valBall E n : Set E), K u z ∂μ ∂μ := integral_integral_swap hint
    _ = _ := by
        simp only [hinner]
        rw [integral_const_mul]

end Main

theorem gauss_core : ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∀ Φ ∈ SBE E, ∃ n₀ : ℤ, ∀ n ≤ n₀,
  ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ =
    (∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ) *
      ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη a Φ hΦ
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  have hσc : σ = conj F E := (eq_one_or_eq_conj σ).resolve_left hσ
  subst hσc
  exact core_of_haar hχ hχ1 hcont (muE E χ) a hΦ

end GlobalTheory.CompanionTheory.WeilSquare
