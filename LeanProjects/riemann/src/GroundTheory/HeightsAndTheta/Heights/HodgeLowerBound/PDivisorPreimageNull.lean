import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDivisorPreimageNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsParamImageNull
import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Set
open ReciprocityTheory.AnForm.A (coordDiv)

theorem volume_coordDiv {D : ℕ} (S : Finset (Fin D)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ S, (fun z : Fin D → ℂ => z i) ⁻¹' {0} := by
    ext z
    simp [coordDiv]
  rw [h]
  exact measure_iUnion_null fun i => measure_iUnion_null fun _ =>
    Measure.pi_eval_preimage_null (fun _ : Fin D => (volume : Measure ℂ)) (measure_singleton 0)

theorem DivisorPreimageNull.proof (h : ParamImageNull.Statement) : DivisorPreimageNull.Statement := by
  intro K _ ι _ P d M R
  classical
  have hloc : ∀ x : M.Xc, ∃ W : Set M.Xc, IsOpen W ∧ x ∈ W ∧ ∃ j : Fin R.N, W ⊆ (R.chart j).source ∧
      ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y ∈ W, s y ∈ mcPts P ∧ M.proj (s y) = y) ∧
        ∀ p, M.atlas.HoloOn W fun y => s y p := by
    intro x
    obtain ⟨U, hU, hxU, s, hs, hhol⟩ := M.sections x
    obtain ⟨j, hj⟩ := R.cover x
    refine ⟨U ∩ (R.chart j).source, hU.inter (R.chart j).open_source,
      ⟨hxU, R.mid_subset_source j (R.inner_subset_mid j hj)⟩, j, inter_subset_right, s,
      fun y hy => hs y hy.1, fun p i => ?_⟩
    exact (hhol p i).mono (inter_subset_inter_right _ (preimage_mono inter_subset_left))
  choose W hWo hxW j hWj s hs hhol using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo (fun x _ => mem_iUnion.2 ⟨x, hxW x⟩)
  let xs : Fin t.card → M.Xc := fun i => (t.equivFin.symm i : M.Xc)
  refine h K ι P d t.card (fun i => R.chart (j (xs i)) '' W (xs i))
    (fun i => R.chart (j (xs i)) '' W (xs i) ∩ coordDiv (R.S (j (xs i))))
    (fun i w => s (xs i) ((R.chart (j (xs i))).symm w)) {z | M.proj z ∉ R.Yo}
    (fun i => (R.chart (j (xs i))).isOpen_image_of_subset_source (hWo _) (hWj _))
    (fun i => inter_subset_left)
    (fun i => measure_mono_null inter_subset_right (volume_coordDiv _)) ?_ ?_
  · rintro i w ⟨y, hyW, rfl⟩
    refine analyticAt_pi_iff.2 fun p => ?_
    exact GroundTheory.Heights₂.Heights.Regular.analyticAt_comp_symm_of_holoOn (R.compat _) (hhol (xs i) p) hyW
      (hWj _ hyW)
  · rintro z ⟨hzY, hz⟩
    obtain ⟨x, hxt, hzW⟩ := mem_iUnion₂.1 (ht (mem_univ (M.proj z)))
    obtain ⟨i, rfl⟩ : ∃ i, xs i = x := ⟨t.equivFin ⟨x, hxt⟩, by simp [xs]⟩
    have hsrc := hWj (xs i) hzW
    have hdiv : R.chart (j (xs i)) (M.proj z) ∈ coordDiv (R.S (j (xs i))) := by
      by_contra hc
      exact hzY ((R.mem_Yo _ _ hsrc).2 hc)
    refine ⟨i, R.chart (j (xs i)) (M.proj z), ⟨⟨M.proj z, hzW, rfl⟩, hdiv⟩, ?_⟩
    have hγ : s (xs i) ((R.chart (j (xs i))).symm (R.chart (j (xs i)) (M.proj z))) = s (xs i) (M.proj z) := by
      rw [(R.chart (j (xs i))).left_inv hsrc]
    rw [hγ]
    obtain ⟨hsm, hsp⟩ := hs (xs i) (M.proj z) hzW
    exact (M.fibre _ hsm z hz).1 hsp

end GroundTheory.Heights₂.Heights.LowerBoundFree
