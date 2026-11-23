import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StProjHoloLocal
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLocalOrbitChart
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicInverse
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem holoOn_comp_compatChart_symm {d : ℕ} {X : Type} [TopologicalSpace X]
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas d X} {e : OpenPartialHomeomorph X (Fin d → ℂ)}
    (he : ReciprocityTheory.AnForm.M.IsCompatChart A e) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g)
    {u : Fin d → ℂ} (hu : u ∈ e.target) (huU : e.symm u ∈ U) :
    DifferentiableAt ℂ (g ∘ e.symm) u := by
  obtain ⟨j, hj⟩ := A.cover (e.symm u)
  have h1 : AnalyticAt ℂ (A.chart j ∘ e.symm) u := (he j).2 u ⟨hu, hj⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart j).symm) ((A.chart j ∘ e.symm) u) := by
    refine hg j _ ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm (A.chart j (e.symm u)) ∈ U
    rw [(A.chart j).left_inv hj]
    exact huU
  have h3 : g ∘ e.symm =ᶠ[𝓝 u] (g ∘ (A.chart j).symm) ∘ (A.chart j ∘ e.symm) := by
    have : ∀ᶠ u' in 𝓝 u, e.symm u' ∈ (A.chart j).source :=
      (e.continuousAt_symm hu).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
    filter_upwards [this] with u' hu'
    simp only [Function.comp, (A.chart j).left_inv hu']
  exact (h2.comp h1).differentiableAt.congr_of_eventuallyEq h3

theorem ProjHoloLocal.proof (hL : LocalOrbitChart.Statement)
    (hO : IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.Statement) : ProjHoloLocal.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D M e he z hz hze

  obtain ⟨N, hNo, hzN, κ, hκ, hκt, hκs⟩ := hL K ι Ω D.y D.n D.arith D.smoothGeneric z hz

  obtain ⟨U, hUo, hxU, s, hs, hsh⟩ := M.sections (M.proj z)
  obtain ⟨c, hc, hcz⟩ := (M.fibre z hz _ (hs _ hxU).1).1 (hs _ hxU).2.symm
  have hsxN : s (M.proj z) ∈ N := by rw [hcz]; exact (hκt z hzN c hc).1
  have hκsx : κ (s (M.proj z)) = κ z := by rw [hcz]; exact (hκt z hzN c hc).2
  have hsd : ∀ u ∈ e.target, e.symm u ∈ U → DifferentiableAt ℂ (s ∘ e.symm) u := fun u hu huU =>
    differentiableAt_pi.2 fun p => holoOn_comp_compatChart_symm he (hsh p) hu huU

  have hex : e (M.proj z) ∈ e.target := e.map_source hze
  have hexU : e.symm (e (M.proj z)) ∈ U := by rw [e.left_inv hze]; exact hxU
  have hTn : e.target ∩ e.symm ⁻¹' U ∩ (s ∘ e.symm) ⁻¹' N ∈ 𝓝 (e (M.proj z)) := by
    refine Filter.inter_mem (Filter.inter_mem (e.open_target.mem_nhds hex) ?_) ?_
    · exact (e.continuousAt_symm hex).preimage_mem_nhds (hUo.mem_nhds hexU)
    · refine (hsd _ hex hexU).continuousAt.preimage_mem_nhds (hNo.mem_nhds ?_)
      show s (e.symm (e (M.proj z))) ∈ N
      rw [e.left_inv hze]
      exact hsxN
  obtain ⟨T, hTsub, hTo, hxT⟩ := mem_nhds_iff.1 hTn
  have hψd : DifferentiableOn ℂ (κ ∘ s ∘ e.symm) T := fun u hu =>
    ((hκ _ (hTsub hu).2).differentiableAt.comp u
      (hsd u (hTsub hu).1.1 (hTsub hu).1.2)).differentiableWithinAt
  have hψi : Set.InjOn (κ ∘ s ∘ e.symm) T := by
    intro u hu u' hu' h
    have h1 := hs _ (hTsub hu).1.2
    have h2 := hs _ (hTsub hu').1.2
    obtain ⟨c', hc', hcc⟩ := hκs _ ⟨(hTsub hu).2, h1.1⟩ _ ⟨(hTsub hu').2, h2.1⟩ h
    have hp : M.proj (s (e.symm u)) = M.proj (s (e.symm u')) :=
      (M.fibre _ h1.1 _ h2.1).2 ⟨c', hc', hcc⟩
    rw [h1.2, h2.2] at hp
    exact e.symm.injOn (hTsub hu).1.1 (hTsub hu').1.1 hp

  obtain ⟨hψo, g, hg, hgψ⟩ := hO D.n T (κ ∘ s ∘ e.symm) hTo hψd hψi

  obtain ⟨O, hOo, hOeq⟩ :=
    continuousOn_iff'.1 M.cont (e.source ∩ e ⁻¹' T) (e.isOpen_inter_preimage hTo)
  refine ⟨O ∩ (N ∩ κ ⁻¹' ((κ ∘ s ∘ e.symm) '' T)),
    hOo.inter (hκ.continuousOn.isOpen_inter_preimage hNo hψo), ?_, g ∘ κ, ?_, ?_⟩
  · refine ⟨?_, hzN, e (M.proj z), hxT, ?_⟩
    · have hz' : z ∈ M.proj ⁻¹' (e.source ∩ e ⁻¹' T) ∩ mcPts (mCoordIdeal D.y) := ⟨⟨hze, hxT⟩, hz⟩
      rw [hOeq] at hz'
      exact hz'.1
    · show κ (s (e.symm (e (M.proj z)))) = κ z
      rw [e.left_inv hze]
      exact hκsx
  · intro w hw
    exact ((hg.differentiableAt (hψo.mem_nhds hw.2.2)).comp w
      (hκ w hw.2.1).differentiableAt).differentiableWithinAt
  · rintro z' ⟨⟨hz'O, hz'N, -⟩, hz'⟩
    have hp : z' ∈ M.proj ⁻¹' (e.source ∩ e ⁻¹' T) ∩ mcPts (mCoordIdeal D.y) := by
      rw [hOeq]
      exact ⟨hz'O, hz'⟩
    obtain ⟨⟨hpe, hpT⟩, -⟩ := hp
    refine ⟨hpe, ?_⟩
    have hpU : M.proj z' ∈ U := by
      have h := (hTsub hpT).1.2
      rwa [Set.mem_preimage, e.left_inv hpe] at h
    obtain ⟨c', hc', hcc⟩ := (M.fibre z' hz' _ (hs _ hpU).1).1 (hs _ hpU).2.symm
    have hκ' : κ (s (M.proj z')) = κ z' := by rw [hcc]; exact (hκt z' hz'N c' hc').2
    have hψz : (κ ∘ s ∘ e.symm) (e (M.proj z')) = κ z' := by
      show κ (s (e.symm (e (M.proj z')))) = κ z'
      rw [e.left_inv hpe]
      exact hκ'
    show e (M.proj z') = g (κ z')
    rw [← hψz, hgψ _ hpT]

end GroundTheory.Heights₂.Heights.LowerBoundFree
