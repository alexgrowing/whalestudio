import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.NormEx
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotEq
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotOpen
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory
open scoped ENNReal

theorem UpperTheory.quotient_haar_measure_pushforward :
    QPush := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _
    μ j ν μ' j' ν' hP hP' U hU π πT hπ hπT hc hμ hν F F' hF hFi hF' hF'i hs hFF
  have hjc : Continuous j := hP.2.1.continuous
  have hUT : IsOpen ((U.comap j : Subgroup T) : Set T) := hU.preimage hjc
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (U.comap j) := hUT.isOpenEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  haveI : SecondCountableTopology (U.comap j) :=
    TopologicalSpace.Subtype.secondCountableTopology ((U.comap j : Subgroup T) : Set T)
  haveI : BorelSpace U := Subtype.borelSpace (U : Set G)
  haveI : BorelSpace (U.comap j) := Subtype.borelSpace ((U.comap j : Subgroup T) : Set T)
  let i : U.comap j →* U := (j.comp (U.comap j).subtype).codRestrict U (fun t => t.2)
  have hi : ∀ t : U.comap j, (i t : G) = j t := fun _ => rfl
  obtain ⟨hPU, hO⟩ := quotOpen_of normEx quotEq G T μ j ν hP U hU i hi
  obtain ⟨ρ', hρc, hρ, -⟩ := normEx H T' μ' j' ν' hP'
  have embG : MeasurableEmbedding (fun u : U => (u : G)) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  have embT : MeasurableEmbedding (fun t : U.comap j => (t : T)) :=
    MeasurableEmbedding.subtype_coe hUT.measurableSet
  have mapG : (μ.comap fun u : U => (u : G)).map (fun u : U => (u : G)) = μ.restrict (U : Set G) := by
    rw [embG.map_comap]; congr 1; exact Subtype.range_coe
  have mapT : (ν.comap fun t : U.comap j => (t : T)).map (fun t : U.comap j => (t : T)) =
      ν.restrict (j ⁻¹' (U : Set G)) := by
    rw [embT.map_comap]; congr 1; exact Subtype.range_coe
  have hρm : Measurable fun h : H => ((ρ' h : NNReal) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp hρc.measurable
  have hn : IsNrm i (ν.comap fun t : U.comap j => (t : T)) (fun u : U => ((ρ' (π u) : NNReal) : ℝ≥0∞)) := by
    refine ⟨hρm.comp (hπ.measurable.comp measurable_subtype_coe), fun x => ?_⟩
    have hg : Measurable fun s : T' => ((ρ' (j' s * π x) : NNReal) : ℝ≥0∞) :=
      hρm.comp ((hP'.2.1.continuous.measurable).mul_const _)
    calc ∫⁻ t, ((ρ' (π ((i t * x : U) : G)) : NNReal) : ℝ≥0∞) ∂(ν.comap fun t : U.comap j => (t : T))
        = ∫⁻ t, (fun s : T => ((ρ' (j' (πT s) * π x) : NNReal) : ℝ≥0∞)) ((fun t : U.comap j => (t : T)) t)
            ∂(ν.comap fun t : U.comap j => (t : T)) := by
          refine lintegral_congr fun t => ?_
          simp only [Subgroup.coe_mul, map_mul, hi, hc]
      _ = ∫⁻ s, ((ρ' (j' (πT s) * π x) : NNReal) : ℝ≥0∞)
            ∂((ν.comap fun t : U.comap j => (t : T)).map (fun t : U.comap j => (t : T))) :=
          (embT.lintegral_map (fun s : T => ((ρ' (j' (πT s) * π x) : NNReal) : ℝ≥0∞))).symm
      _ = ∫⁻ s, ((ρ' (j' (πT s) * π x) : NNReal) : ℝ≥0∞) ∂(ν.restrict (j ⁻¹' (U : Set G))) := by
          rw [mapT]
      _ = ∫⁻ s, ((ρ' (j' s * π x) : NNReal) : ℝ≥0∞) ∂((ν.restrict (j ⁻¹' (U : Set G))).map πT) :=
          (lintegral_map hg hπT.measurable).symm
      _ = ∫⁻ s, ((ρ' (j' s * π x) : NNReal) : ℝ≥0∞) ∂ν' := by rw [hν]
      _ = 1 := hρ.2 (π x)
  have hFU : Measurable fun u : U => F u := hF.comp measurable_subtype_coe
  have hFUi : ∀ (t : U.comap j) (g : U), F ((i t * g : U) : G) = F g := by
    intro t g
    rw [Subgroup.coe_mul, hi, hFi]
  have hgm : Measurable fun h : H => F' h * ((((ρ' h : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) :=
    hF'.mul (Complex.measurable_ofReal.comp hρm.ennreal_toReal)
  have e1 := (hO F hF hFi hs).2
  have e2 := (quotEq (↥U) (↥(U.comap j)) (μ.comap fun u : U => (u : G)) i
    (ν.comap fun t : U.comap j => (t : T)) hPU (fun u : U => F u) hFU hFUi _ hn).2.2
  have e3 := (quotEq H T' μ' j' ν' hP' F' hF' hF'i _ hρ).2.2
  rw [e1, e2, e3]
  calc ∫ u : U, F u * ((((ρ' (π u) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) ∂(μ.comap fun u : U => (u : G))
      = ∫ u : U, (fun x : G => F' (π x) * ((((ρ' (π x) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ))
            ((fun u : U => (u : G)) u) ∂(μ.comap fun u : U => (u : G)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [hFF u u.2]
    _ = ∫ x, F' (π x) * ((((ρ' (π x) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ)
          ∂((μ.comap fun u : U => (u : G)).map (fun u : U => (u : G))) :=
        (embG.integral_map (fun x : G => F' (π x) * ((((ρ' (π x) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ))).symm
    _ = ∫ x, F' (π x) * ((((ρ' (π x) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) ∂(μ.restrict (U : Set G)) := by
        rw [mapG]
    _ = ∫ h, F' h * ((((ρ' h : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) ∂((μ.restrict (U : Set G)).map π) :=
        (integral_map hπ.aemeasurable hgm.aestronglyMeasurable).symm
    _ = ∫ h, F' h * ((((ρ' h : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) ∂μ' := by rw [hμ]
