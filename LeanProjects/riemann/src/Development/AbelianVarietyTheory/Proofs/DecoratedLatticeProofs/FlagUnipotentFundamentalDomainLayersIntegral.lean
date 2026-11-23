import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagUnipotentCoordinateMeasurableEquivStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarCovolumeOneSkewHermitianAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SFiniteCovolumeOneMatrixUnitriangularMeasuresStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentHaarEqMapCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittFlagUnipotentFixerFundamentalDomainLayersStatement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

set_option maxHeartbeats 1000000 in

theorem layers_integral : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ), ∃ 𝓐 : Set (flagN d), IsFundamentalDomain ((GQ V ⊓ radX d).subgroupOf (flagN d)) 𝓐 vN.ν ∧ ∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν := by
  intro D V V₀ ρ d vN vb vU
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_flagUnipotent_coordinate_measurableEquiv D V V₀ ρ d
  obtain ⟨lC, 𝓒, hH, hS, hF, h1⟩ := GlobalTheory.T.exists_haar_covolume_one_skewHermitian_adelic D ρ
  obtain ⟨sb, su⟩ := GlobalTheory.T.sFinite_covolume_one_matrix_unitriangular_measures D ρ V₀.rank vb vU
  have hν := GlobalTheory.T.flagUnipotentHaar_eq_map_coordinates D V V₀ ρ d vN vb vU e he lC 𝓒 hH hS hF h1
  refine ⟨e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ)), ?_, ?_⟩
  · rw [hν]; exact GlobalTheory.T.wittFlagUnipotentFixer_fundamentalDomain_layers D V V₀ ρ d e he lC 𝓒 hH hS hF vb vU.ν sb su
  · intro f hf hinv
    have hg : Measurable fun p => f (e p : GA D V) := hf.comp (measurable_subtype_coe.comp e.measurable)
    let g : Mx D ρ V₀.rank × UX D ρ → ENNReal := fun q => f (e (0, q) : GA D V)
    have hgm : Measurable g := hg.comp (measurable_const.prodMk measurable_id)
    have hge : ∀ q, g q = f (d.nB q.1 * d.levi q.2.1) := fun q => by
      show f (e (0, q) : GA D V) = _
      rw [he, d.nC_zero, one_mul]
    have hpt : ∀ p : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ), f (e p : GA D V) = g p.2 := fun p => by
      have hm : (e (0, p.2) : GA D V) ∈ flagN d := (e (0, p.2)).2
      rw [he, d.nC_zero, one_mul] at hm
      rw [hge, he, hinv _ _ hm]
    have s1 : ∫⁻ n in e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ)), f n.1 ∂((lC.prod (vb.μ.prod vU.ν)).map e) =
        ∫⁻ p in 𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ), f (e p : GA D V) ∂(lC.prod (vb.μ.prod vU.ν)) := by
      rw [e.restrict_map, lintegral_map_equiv, e.preimage_image]
    have s2 : (lC.prod (vb.μ.prod vU.ν)).restrict (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ)) = (lC.restrict 𝓒).prod ((vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ)) :=
      (Measure.prod_restrict 𝓒 (vb.𝓕 ×ˢ Set.univ)).symm
    have s3 : (vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ) = (vb.μ.restrict vb.𝓕).prod vU.ν := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    have s4 : ∫⁻ p, g p.2 ∂((lC.restrict 𝓒).prod ((vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ))) =
        ∫⁻ q, g q ∂((vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ)) := by
      rw [lintegral_prod (fun p : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) => g p.2) (hgm.comp measurable_snd).aemeasurable]
      show ∫⁻ _ in 𝓒, (∫⁻ y in vb.𝓕 ×ˢ Set.univ, g y ∂(vb.μ.prod vU.ν)) ∂lC = _
      rw [lintegral_const, Measure.restrict_apply_univ, h1, mul_one]
    have s5 : ∫⁻ q, g q ∂((vb.μ.restrict vb.𝓕).prod vU.ν) = ∫⁻ u, ∫⁻ b in vb.𝓕, g (b, u) ∂vb.μ ∂vU.ν := by
      rw [lintegral_prod _ hgm.aemeasurable]
      exact lintegral_lintegral_swap (f := fun b u => g (b, u)) hgm.aemeasurable
    have s6 : ∫⁻ p in 𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ), f (e p : GA D V) ∂(lC.prod (vb.μ.prod vU.ν)) =
        ∫⁻ p, g p.2 ∂((lC.restrict 𝓒).prod ((vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ))) := by
      rw [s2]; exact lintegral_congr fun p => hpt p
    rw [hν]
    refine s1.trans (s6.trans (s4.trans ?_))
    rw [s3]
    refine s5.trans ?_
    exact lintegral_congr fun u => lintegral_congr fun b => hge (b, u)

end GlobalTheory.Unf

end
