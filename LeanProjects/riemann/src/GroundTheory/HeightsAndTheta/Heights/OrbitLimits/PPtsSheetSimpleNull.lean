import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSheetSimpleNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsGenericCount
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetB
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet segre_differentiableAt)

theorem PtsSheetSimpleNull.simple_of_count {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {d : ℕ} {y : Fin e → ℂ}
    (hbd : ∀ y', (fibre P Ψ y').encard ≤ d) (hy : (fibre P Ψ y).encard = d)
    (hsh : ∀ w ∈ fibre P Ψ y, ∃ γ, IsSheet P Ψ y w γ) {w : ((k : K) → ι k) → ℂ}
    (hw : w ∈ fibre P Ψ y) : IsSimpleSheetPt P Ψ w := by
  have hF : (fibre P Ψ y).Finite := Set.finite_of_encard_eq_coe hy
  choose! γ hγ using hsh
  obtain ⟨U, hU, hdisj⟩ := hF.t2_separation

  have hev : ∀ᶠ y' in 𝓝 y, ∀ a ∈ fibre P Ψ y,
      (γ a y' ∈ mcPts P ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧ segre (γ a y') ∈ U a := by
    refine (hF.eventually_all).2 fun a ha => ?_
    have hc := (segre_differentiableAt (hγ a ha).2.self_of_nhds.1).continuousAt
    have hmem : U a ∈ 𝓝 (segre (γ a y)) := by
      rw [(hγ a ha).1]
      exact (hU a).2.mem_nhds (hU a).1
    filter_upwards [(hγ a ha).2, hc.preimage_mem_nhds hmem] with y' h1 h2
    exact ⟨⟨h1.2.1, h1.2.2⟩, h2⟩

  have hfib : ∀ y', (∀ a ∈ fibre P Ψ y, (γ a y' ∈ mcPts P ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧
      segre (γ a y') ∈ U a) → fibre P Ψ y' = (fun a => segre (γ a y')) '' fibre P Ψ y := by
    intro y' h
    have hinj : Set.InjOn (fun a => segre (γ a y')) (fibre P Ψ y) := by
      intro a ha b hb hab
      by_contra hne
      exact Set.disjoint_left.mp (hdisj ha hb hne) (h a ha).2 (by simp only at hab; rw [hab]; exact (h b hb).2)
    have hsub : (fun a => segre (γ a y')) '' fibre P Ψ y ⊆ fibre P Ψ y' := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨γ a y', (h a ha).1.1, rfl, (h a ha).1.2⟩
    refine ((hF.image _).eq_of_subset_of_encard_le hsub ?_).symm
    rw [hinj.encard_image, hy]
    exact hbd y'
  refine ⟨y, γ w, hγ w hw, ?_⟩
  filter_upwards [hev.prodMk_nhds ((hU w).2.mem_nhds (hU w).1)] with q hq hq2
  rw [hfib q.1 hq.1] at hq2
  obtain ⟨a, ha, hqa⟩ := hq2
  have haw : a = w := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj ha hw hne) (by rw [← hqa]; exact (hq.1 a ha).2) hq.2
  rw [← hqa, haw]

theorem PtsSheetSimpleNull.proof (hG : PtsGenericCount.Statement) : PtsSheetSimpleNull.Statement := by
  intro K _ ι _ P e Ψ hP hΨ
  obtain ⟨d, hbd, hnull⟩ := hG K ι P e Ψ hP hΨ
  refine measure_mono_null (fun y hy => ?_) hnull
  obtain ⟨w, hw, -, hns⟩ := hy
  exact fun hgood => hns (PtsSheetSimpleNull.simple_of_count hbd hgood.1 hgood.2 hw)

end GroundTheory.Heights₂.Heights
