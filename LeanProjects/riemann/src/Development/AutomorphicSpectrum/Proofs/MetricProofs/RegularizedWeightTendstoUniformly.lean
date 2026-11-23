import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2Statement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem tendstoUniformlyOn_regWeight_of_isTied :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing J)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, J k) → ℂ)) (A : HermLine J) (S : LogLogRegularisationSetting M Xo A), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  intro K _ J _ P n M Xo A S hS K' hK'Y hK'
  refine hK'.induction_on (p := fun s => TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) s)
    ?_ ?_ ?_ ?_
  · intro u _
    simp
  · intro s t hst ht
    exact ht.mono hst
  · intro s t hs ht
    intro u hu
    filter_upwards [hs u hu, ht u hu] with a ha hb y hy
    exact hy.elim (ha y) (hb y)
  · intro x hx
    obtain ⟨j, hj⟩ := M.atlas.cover x
    have hopen : (M.atlas.chart j).source ∈ 𝓝 x := (M.atlas.chart j).open_source.mem_nhds hj
    obtain ⟨C, hCn, hCs, hCc⟩ := local_compact_nhds hopen
    refine ⟨C ∩ K', ?_, ?_⟩
    · exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hCn) self_mem_nhdsWithin
    · have hcpt : IsCompact (C ∩ K') := hCc.inter hK'
      have himg : IsCompact ((M.atlas.chart j) '' (C ∩ K')) :=
        hcpt.image_of_continuousOn
          ((M.atlas.chart j).continuousOn.mono fun y hy => hCs hy.1)
      have hsub : (M.atlas.chart j) '' (C ∩ K') ⊆
          (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo := by
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨(M.atlas.chart j).map_source (hCs hy.1), ?_⟩
        show (M.atlas.chart j).symm ((M.atlas.chart j) y) ∈ S.R.Yo
        rw [(M.atlas.chart j).left_inv (hCs hy.1)]
        exact hK'Y hy.2
      have hu := (GlobalTheory.T.regularized_weight_tendsto_C2 K J P n M Xo A S hS j _ hsub himg).1
      rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
      intro ε hε
      filter_upwards [hu ε hε] with t ht y hy
      have h := ht _ (Set.mem_image_of_mem _ hy)
      simpa [Function.comp, (M.atlas.chart j).left_inv (hCs hy.1)] using h

end GlobalTheory.CompanionTheory.Ar.Cusp
