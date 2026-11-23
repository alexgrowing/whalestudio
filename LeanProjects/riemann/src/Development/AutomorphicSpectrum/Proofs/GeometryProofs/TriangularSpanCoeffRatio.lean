import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem diag_compare_of_triIn : ∀ (V F EC : Type) [CommRing V] [Field F] [Algebra V F] [AddCommGroup EC] [Module F EC] [Module V EC] [IsScalarTower V F EC] (r : ℕ) (u v w : Fin r → EC) (a b : Fin r → F) (d : V), LinearIndependent F u → FinRd.Roots.TriIn u a v → FinRd.Roots.TriIn u b w → (∀ i, b i ≠ 0) → (∀ x ∈ Submodule.span V (Set.range v), d • x ∈ Submodule.span V (Set.range w)) → ∀ i, ∃ c : V, algebraMap V F d * a i = algebraMap V F c * b i := by
  intro V F EC _ _ _ _ _ _ _ r u v w a b d hu hv hw hb hd i
  classical
  obtain ⟨e, he⟩ :=
    (Submodule.mem_span_range_iff_exists_fun V).1 (hd (v i) (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨cv, hcvi, hcv0, hvi⟩ := hv i
  choose cw hcwd hcw0 hw' using hw
  have key : ∀ m, algebraMap V F d * cv m = ∑ j, algebraMap V F (e j) * cw j m := by
    have hL : d • v i = ∑ m, (algebraMap V F d * cv m) • u m := by
      rw [hvi, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_smul, algebraMap_smul]
    have hR : ∑ j, e j • w j = ∑ m, (∑ j, algebraMap V F (e j) * cw j m) • u m := by
      simp_rw [hw', Finset.smul_sum, Finset.sum_smul, mul_smul, algebraMap_smul]
      exact Finset.sum_comm
    have h1 : ∑ m, (algebraMap V F d * cv m - ∑ j, algebraMap V F (e j) * cw j m) • u m = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, ← hL, ← hR, he, sub_self]
    intro m
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hu _ h1 m)
  have hzero : ∀ j, i < j → algebraMap V F (e j) = 0 := by
    by_contra hcon
    push_neg at hcon
    set S := Finset.univ.filter (fun j => i < j ∧ algebraMap V F (e j) ≠ 0) with hSdef
    have hS : S.Nonempty := by
      obtain ⟨j, hj⟩ := hcon
      exact ⟨j, by simp [S, hj]⟩
    obtain ⟨J, hJS, hJmax⟩ : ∃ J ∈ S, ∀ j ∈ S, j ≤ J :=
      ⟨S.max' hS, S.max'_mem hS, fun j hj => S.le_max' j hj⟩
    have hJ : i < J ∧ algebraMap V F (e J) ≠ 0 := by simpa [S] using hJS
    have hmax : ∀ j, J < j → algebraMap V F (e j) = 0 := by
      intro j hj
      by_contra hne
      have hjS : j ∈ S := by simp [S, hne, hJ.1.trans hj]
      exact not_le.2 hj (hJmax j hjS)
    have hk := key J
    rw [hcv0 J hJ.1, mul_zero, Finset.sum_eq_single J, hcwd J] at hk
    · exact hJ.2 ((mul_eq_zero.1 hk.symm).resolve_right (hb J))
    · intro j _ hjJ
      rcases lt_or_gt_of_ne hjJ with h | h
      · rw [hcw0 j J h, mul_zero]
      · rw [hmax j h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ J) h
  refine ⟨e i, ?_⟩
  have hk := key i
  rw [hcvi, Finset.sum_eq_single i, hcwd i] at hk
  · exact hk
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hcw0 j i h, mul_zero]
    · rw [hzero j h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
