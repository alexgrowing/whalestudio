import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermProjectionImageNear
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermRegularDimGe
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreNear
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularLocusDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicIsolatedFibreOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicFibreInfinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Set

theorem le_of_isolated_fibres (hfi : HolomorphicFibreInfinite.Statement) {e d : ℕ} {O : Set (Fin e → ℂ)}
    {φ : (Fin e → ℂ) → Fin d → ℂ} (hO : IsOpen O) (hne : O.Nonempty) (hφ : DifferentiableOn ℂ φ O)
    (hiso : ∀ t ∈ O, ∃ W ∈ 𝓝 t, ∀ v ∈ W, v ∈ O → φ v = φ t → v = t) : e ≤ d := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨ρ, hρ, hρO⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hO.mem_nhds hy0)
  obtain ⟨y, hy⟩ := hfi e d (ball y0 ρ) φ hlt isOpen_ball ⟨y0, mem_ball_self hρ⟩
    (hφ.mono (ball_subset_closedBall.trans hρO))
  obtain ⟨p, hpK, hpacc⟩ := hy.exists_accPt_of_subset_isCompact (isCompact_closedBall y0 ρ)
    (fun t ht => ball_subset_closedBall ht.1)
  have hpO : p ∈ O := hρO hpK
  have hcl : p ∈ closure {t | t ∈ ball y0 ρ ∧ φ t = y} := mem_closure_iff_nhds.2 fun U hU => by
    obtain ⟨q, hq, -⟩ := accPt_iff_nhds.1 hpacc U hU
    exact ⟨q, hq⟩
  have hφp : φ p = y := by
    have h1 := mem_closure_image ((hφ p hpO).differentiableAt (hO.mem_nhds hpO)).continuousAt hcl
    have h2 : φ '' {t | t ∈ ball y0 ρ ∧ φ t = y} ⊆ {y} := by
      rintro _ ⟨t, ht, rfl⟩
      exact ht.2
    simpa using closure_mono h2 h1
  obtain ⟨W, hW, hWiso⟩ := hiso p hpO
  obtain ⟨q, ⟨hqW, hqB, hqy⟩, hqp⟩ := accPt_iff_nhds.1 hpacc W hW
  exact hqp (hWiso q hqW (hρO (ball_subset_closedBall hqB)) (hqy.trans hφp.symm))

theorem IrreducibleGermProjectionImageNear.proof (hdim : IrreducibleGermRegularDimGe.Statement)
    (hisoN : IsolatedFibreNear.Statement) (hreg : RegularLocusDense.Statement)
    (hopen : HolomorphicIsolatedFibreOpen.Statement) (hfi : HolomorphicFibreInfinite.Statement) :
    IrreducibleGermProjectionImageNear.Statement := by
  intro σ _ X w d A hX hirr hfin hnd
  obtain ⟨N1, hN1, hdimN⟩ := hdim σ X w d A hX hirr hfin hnd
  obtain ⟨N2, hN2, hisoX⟩ := hisoN σ X w d A hX hfin
  obtain ⟨N3, hN3o, hwN3, hdense⟩ := hreg σ X w hX
  refine ⟨interior (N1 ∩ N2) ∩ N3,
    inter_mem (interior_mem_nhds.2 (inter_mem hN1 hN2)) (hN3o.mem_nhds hwN3), ?_⟩
  have hBo : IsOpen (interior (N1 ∩ N2) ∩ N3) := isOpen_interior.inter hN3o
  rintro x ⟨hxX, hxB⟩ h hh hvan
  obtain ⟨ε, hε, hhb⟩ := hh.exists_ball_analyticOnNhd
  obtain ⟨V, hV, hVo, hxV⟩ := _root_.mem_nhds_iff.1 hvan
  set V1 := V ∩ (interior (N1 ∩ N2) ∩ N3) ∩ A ⁻¹' ball (A x) ε with hV1
  have hV1o : IsOpen V1 := (hVo.inter hBo).inter (isOpen_ball.preimage A.continuous)
  have hxV1 : x ∈ V1 := ⟨⟨hxV, hxB⟩, mem_ball_self hε⟩
  have hcl := hdense V1 hV1o (fun z hz => hz.1.2.2) ⟨hxX, hxV1⟩
  obtain ⟨r, hr⟩ : (regLocus (X ∩ V1)).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    rw [hemp, closure_empty] at hcl
    exact hcl
  obtain ⟨hrX, e, A', O, V', g, hO, hV', hrV', hg, hA'g, hXV'⟩ := hr
  have hgX : ∀ t ∈ O, g t ∈ X ∩ V1 := fun t ht => by
    have : g t ∈ X ∩ V1 ∩ V' := hXV' ▸ mem_image_of_mem g ht
    exact this.1
  have hN12 : ∀ z ∈ V1, z ∈ N1 ∩ N2 := fun z hz => interior_subset hz.1.2.1
  have hchart : X ∩ (V1 ∩ V') = g '' O := by rw [← hXV']; exact (inter_assoc X V1 V').symm
  have hde : d ≤ e := hdimN r ⟨hrX.1, (hN12 r hrX.2).1⟩ e A' O (V1 ∩ V') g hO (hV1o.inter hV')
    ⟨hrX.2, hrV'⟩ hg hA'g hchart
  have hφ : DifferentiableOn ℂ (fun y => A (g y)) O :=
    A.differentiable.comp_differentiableOn hg.differentiableOn
  have hisoC : ∀ t ∈ O, ∃ W ∈ 𝓝 t, ∀ v ∈ W, v ∈ O → A (g v) = A (g t) → v = t := by
    intro t ht
    obtain ⟨W, hW, hiW⟩ := hisoX (g t) ⟨(hgX t ht).1, (hN12 _ (hgX t ht).2).2⟩
    refine ⟨g ⁻¹' W, (hg t ht).continuousAt.preimage_mem_nhds hW, fun v hvW hvO hv => ?_⟩
    have hgv := hiW (g v) ⟨(hgX v hvO).1, hvW⟩ hv
    rw [← hA'g v hvO, ← hA'g t ht, hgv]
  obtain ⟨y0, hy0O, hy0r⟩ : r ∈ g '' O := hXV' ▸ ⟨hrX, hrV'⟩
  have hed : e ≤ d := le_of_isolated_fibres hfi hO ⟨y0, hy0O⟩ hφ hisoC
  obtain rfl : e = d := le_antisymm hed hde
  have hop := hopen e O (fun y => A (g y)) y0 hO hy0O hφ (hisoC y0 hy0O) O (hO.mem_nhds hy0O)
  have hzero : ∀ y ∈ (fun y => A (g y)) '' O, h y = 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact hV (hgX t ht).2.1.1 (hgX t ht).1
  have hAr : A (g y0) ∈ ball (A x) ε := (hgX y0 hy0O).2.2
  have hEq : EqOn h 0 (ball (A x) ε) :=
    hhb.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hAr
      (Filter.mem_of_superset hop fun y hy => hzero y hy)
  filter_upwards [ball_mem_nhds (A x) hε] with y hy using hEq hy

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
