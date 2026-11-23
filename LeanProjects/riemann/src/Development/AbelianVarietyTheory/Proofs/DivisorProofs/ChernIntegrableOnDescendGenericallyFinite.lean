import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleChartCoveringComplexPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartPreimageOfFiniteLiftedChartCoveringStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernDescend

theorem chernIntegrableOn_descend : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (ρ : Y' ⟶ Y), IsArithVar (ρ ≫ q) e → ρ (genericPoint Y') = genericPoint Y → ρ.residueDegree (genericPoint Y') ≠ 0 → ∀ (N : HermLB q) (σ : k →+* ℂ) (U : Y.Opens) (f : CxPts q σ → ℝ), ContinuousOn f (ptsIn q σ U) → ((N.restr ρ).φ σ).ChernIntegrableOn e (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (fun y => f (PtsOver.map ρ rfl _ y)) → (N.φ σ).ChernIntegrableOn e (ptsIn q σ U) f := by
  intro k _ Y _ q e hY Y' _ ρ hY' hη hδ N σ U f hf hint
  obtain ⟨V, hVη, hV⟩ := GlobalTheory.T.exists_open_etaleChart_covering_complexPoints hY hY' ρ rfl hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hV σ
  have hFm : Measurable (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ)) :=
    (PtsOver.continuous_map _ _ _).measurable
  have hpre : ∀ W : Y.Opens, PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' ptsIn q σ W =
      ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ W) := by
    intro W
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hUm : MeasurableSet (ptsIn q σ U) := (isOpen_ptsIn U).measurableSet
  have hVm : MeasurableSet (ptsIn q σ V) := (isOpen_ptsIn V).measurableSet
  have h0 : ∀ ε : ℤˣ, (N.φ σ).chernPart e ε (ptsIn q σ V)ᶜ = 0 := by
    intro ε
    have h := GlobalTheory.T.chernPart_over_properClosed_eq_zero hY ((V : Y.Opens) : Set Y)ᶜ V.isOpen.isClosed_compl (by simp [hVη]) σ
      (N.φ σ) ε
    convert h using 2
    ext y
    simp [mem_ptsIn]
  have hmeas : ∀ ε : ℤˣ, (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) •
      ((N.φ σ).chernPart e ε).restrict (ptsIn q σ U) =
      Measure.map (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ))
        ((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
          (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) := by
    intro ε
    ext A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA, Measure.map_apply hFm hA,
      Measure.restrict_apply (hFm hA), ← Set.preimage_inter,
      GlobalTheory.T.chernPart_preimage_of_finite_liftedChartCovering hY hY' ρ rfl (N.φ σ) (N.cInf σ) ε (ptsIn q σ V) (isOpen_ptsIn V) _ hcard hchart
        hlift (fun c c' hc w hw => GlobalTheory.T.chernDensity_pullbackWeight_in_liftedChart ρ rfl (N.φ σ) (N.cInf σ) c c' hc w hw) _
        (hA.inter (hUm.inter hVm)) (fun x hx => hx.2.2), smul_eq_mul, ← Set.inter_assoc,
      measure_inter_conull (h0 ε)]
  have hδ1 : (1 : ℝ≥0∞) ≤ (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) :=
    Nat.one_le_cast.2 (Nat.pos_of_ne_zero hδ)
  have key : ∀ ε : ℤˣ, IntegrableOn (fun y => f (PtsOver.map ρ rfl _ y))
      (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (((N.φ σ).pull ρ rfl).chernPart e ε) →
      IntegrableOn f (ptsIn q σ U) ((N.φ σ).chernPart e ε) := by
    intro ε h
    refine ⟨hf.aestronglyMeasurable hUm, ?_⟩
    have h1 := h.2
    unfold HasFiniteIntegral at h1 ⊢
    refine lt_of_le_of_lt ?_ h1
    calc ∫⁻ y, ‖f y‖ₑ ∂((N.φ σ).chernPart e ε).restrict (ptsIn q σ U)
        ≤ (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) *
          ∫⁻ y, ‖f y‖ₑ ∂((N.φ σ).chernPart e ε).restrict (ptsIn q σ U) :=
          le_mul_of_one_le_left' hδ1
      _ = ∫⁻ y, ‖f y‖ₑ ∂Measure.map (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ))
          ((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
            (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) := by
          rw [← hmeas ε, lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ z, ‖f (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) z)‖ₑ
          ∂((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
            (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) :=
          lintegral_map_le _ _
      _ ≤ _ := by
          refine lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl
          rw [← hpre U]
          exact Set.preimage_mono Set.inter_subset_left
  exact ⟨key 1 hint.1, key (-1) hint.2⟩

end GlobalTheory.ChernDescend

end
