import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecGen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

theorem ModelGenerated.proof : ModelGenerated.Statement := by
  classical
  intro F _ K _ _ ι _ Ω _ _ y k₀ hy β
  obtain ⟨i₀, -⟩ := hy.1 k₀
  have hcard : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hcard).symm⟩
  let e : ι k₀ ≃ Fin (N + 1) := (Fintype.equivFin _).trans (finCongr hN)
  set x := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm with hx
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hy β
  obtain ⟨c₀, hc₀⟩ := Kleiman.Generated.full.{0, 0} F Ω N x Q
  refine ⟨c₀, fun c hc => ?_⟩
  set δ := β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ with hδ
  set L := Q.tensor (Kleiman.twistBundle F x c) with hL
  have hLsys : L.toSubSystem = Q.toSubSystem.twist (Kleiman.twistSys F x c) := rfl
  have hgen : L.toSubSystem.Generated := by rw [hLsys]; exact hc₀ c hc
  have hsecs : L.toSubSystem.secs = secOver F y δ := by rw [hLsys, hQ c]

  have hgam : ∀ m : ℤ, L.toSubSystem.gam m = secOver F y (δ + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro m
    rw [Kleiman.SubSystem.gam, hLsys, Kleiman.SubSystem.twist_assoc, Kleiman.twistSys_twist_twistSys, hQ (c + m),
      hδ, add_smul, add_assoc]

  have hsub : ∀ I : Kleiman.Chart x, (L.sub I : Set Ω) = chartSecOver F y k₀ e δ I := by
    intro I
    ext t
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [hgam]

  have hfg : ∀ I : Kleiman.Chart x, ∃ G : Finset Ω, Submodule.span (Kleiman.chartRing F x I) (G : Set Ω) = L.sub I :=
    fun I => L.fg I
  choose G hG using hfg
  have hfin : ∀ (I : Kleiman.Chart x) (g : Ω), ∃ T : Finset Ω, (T : Set Ω) ⊆ L.toSubSystem.secs ∧
      (g ∈ L.sub I → g ∈ Submodule.span (Kleiman.chartRing F x I) (T : Set Ω)) := by
    intro I g
    by_cases hg : g ∈ L.sub I
    · rw [← hgen I] at hg
      obtain ⟨T, hT, hgT⟩ := Submodule.mem_span_finite_of_mem_span hg
      exact ⟨T, hT, fun _ => hgT⟩
    · exact ⟨∅, by simp, fun h => absurd h hg⟩
  choose T hTsec hTspan using hfin
  let U : Finset Ω := Finset.univ.biUnion fun I => (G I).biUnion fun g => T I g
  have hU : (U : Set Ω) ⊆ L.toSubSystem.secs := by
    intro s hs
    simp only [U, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
      Finset.mem_coe] at hs
    obtain ⟨I, g, -, hs⟩ := hs
    exact hTsec I g hs
  have hspanU : ∀ I : Kleiman.Chart x, Submodule.span (Kleiman.chartRing F x I) (U : Set Ω) = L.sub I := by
    intro I
    apply le_antisymm
    · rw [← hgen I]
      exact Submodule.span_mono hU
    · rw [← hG I, Submodule.span_le]
      intro g hg
      have hgI : g ∈ L.sub I := by rw [← hG I]; exact Submodule.subset_span hg
      refine Submodule.span_mono ?_ (hTspan I g hgI)
      intro s hs
      simp only [U, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
        Finset.mem_coe]
      exact ⟨I, g, hg, hs⟩
  let η : Fin U.card → Ω := fun j => (U.equivFin.symm j : Ω)
  have hrange : Set.range η = (U : Set Ω) := by
    ext s
    constructor
    · rintro ⟨j, rfl⟩
      exact (U.equivFin.symm j).2
    · intro hs
      exact ⟨U.equivFin ⟨s, hs⟩, by simp [η]⟩
  have hη : ∀ j, η j ∈ secOver F y δ := fun j => hsecs ▸ hU (hrange ▸ Set.mem_range_self j)
  refine ⟨U.card, η, hη, ?_⟩
  refine (ChartSecGen.full F K ι Ω y k₀ N e hy δ U.card η hη).mpr fun I => ?_
  rw [hrange, hspanU I, hsub I]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
