import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicChartsGenericPointProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonKernelHessiansPullbackSmallerChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericP
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixDrop

theorem part_pull_eq_zero : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D D' : ℕ), D' < D → IsProjOver p → topologicalKrullDim X = (D' : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (L : Fin D → MLine p σ) (ε : ℤˣ), part (fun i => (L i).pull π hπ) ε = 0 := by
  intro F _ X Y _ _ p q σ D D' hD hp hX hq π hπ hgen L ε
  have hLN : IsLocallyNoetherian X := by
    obtain ⟨N, ι, _, h⟩ := hp
    have : LocallyOfFiniteType p := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U, hU, hch⟩ := GlobalTheory.GenericCharts.exists_generic_charts F X p σ D' hp hX
  have hgU : genericPoint Y ∈ π ⁻¹ᵁ U := by
    show π (genericPoint Y) ∈ U
    rw [hgen]; exact hU
  have hnull := GlobalTheory.MixNull.part_compl_null F Y q σ σ.injective hq D (fun i => (L i).pull π hπ) ε (π ⁻¹ᵁ U) hgU
  have hz : ∀ (c : AlgChart q σ D) (w : CxPts q σ), w ∈ c.e.source → w ∈ ptsIn q σ (π ⁻¹ᵁ U) →
      dens (fun i => (L i).pull π hπ) c w = 0 := by
    intro c w hw hwU
    have hm : ptMap π hπ σ w ∈ ptsIn p σ U := by
      rw [mem_ptsIn] at hwU ⊢
      exact hwU
    obtain ⟨c0, hc0⟩ := hch _ hm
    obtain ⟨ξ, hξ, hker⟩ := GlobalTheory.T.exists_common_kernel_hessians_pullback_smaller_chart F X Y p q σ D D' hD π hπ c0 c w hw hc0
    have hdet : ∀ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
        c.hess ((L (τ l)).pull π hπ).φ (pick ((L (τ l)).pull π hπ).φ.isLB w) w j l).det = 0 := by
      intro τ
      refine (Matrix.exists_vecMul_eq_zero_iff).1 ⟨ξ, hξ, funext fun l => ?_⟩
      have h1 := congrFun (hker (L (τ l)) (pick ((L (τ l)).pull π hπ).φ.isLB w) (mem_pick _ w)) l
      simpa [Matrix.vecMul, dotProduct] using h1
    unfold dens
    simp only [hdet, Finset.sum_const_zero, Complex.zero_re, mul_zero]
  have hc : ∀ c : AlgChart q σ D, chartMeas c.e
      (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) = 0 := by
    intro c
    set S := ptsIn q σ (π ⁻¹ᵁ U) with hSdef
    have hS : MeasurableSet S := (isOpen_ptsIn _).measurableSet
    have h1 : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) S = 0 := by
      rw [chartMeas_apply c.e _ hS]
      refine (setLIntegral_congr_fun (measurableSet_image _ (c.e.open_source.measurableSet.inter hS)
        inter_subset_left) ?_).trans lintegral_zero
      rintro _ ⟨y, hy, rfl⟩
      show ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c (c.e.symm (c.e y))) = 0
      rw [c.e.left_inv hy.1, hz c y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero]
    have hle : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) ≤
        part (fun i => (L i).pull π hπ) ε :=
      le_iSup (fun c : AlgChart q σ D => chartMeas c.e
        (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y))) c
    have h2 := (Measure.le_iff'.1 hle Sᶜ).trans_eq hnull
    refine Measure.measure_univ_eq_zero.1 (le_antisymm ?_ bot_le)
    calc _ ≤ _ := measure_mono (show univ ⊆ S ∪ Sᶜ by simp)
      _ ≤ _ := measure_union_le _ _
      _ ≤ 0 := by rw [h1, zero_add]; exact h2
  show glueMeas _ _ = 0
  unfold glueMeas
  simp only [hc]
  exact le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)

end GlobalTheory.MixDrop
