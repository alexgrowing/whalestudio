import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfIsAnalyticSubset

namespace GlobalTheory.AnUnion
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt

variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem isAnalyticSubset_union {A : FinHolAtlas d X} {S T : Set X} (hS : A.IsAnalyticSubset S)
    (hT : A.IsAnalyticSubset T) : A.IsAnalyticSubset (S ∪ T) := by
  intro x
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  obtain ⟨W', hW', hxW', r', f', hf', hTW⟩ := hT x
  refine ⟨W ∩ W', hW.inter hW', ⟨hxW, hxW'⟩, r * r',
    fun k y => f (finProdFinEquiv.symm k).1 y * f' (finProdFinEquiv.symm k).2 y,
    fun k j => ?_, ?_⟩
  · have h1 : A.HoloOn (W ∩ W') (f (finProdFinEquiv.symm k).1) :=
      fun j => (hf _ j).mono fun z hz => ⟨hz.1, hz.2.1⟩
    have h2 : A.HoloOn (W ∩ W') (f' (finProdFinEquiv.symm k).2) :=
      fun j => (hf' _ j).mono fun z hz => ⟨hz.1, hz.2.2⟩
    exact (h1 j).mul (h2 j)
  · ext y
    constructor
    · rintro ⟨hy, hyW, hyW'⟩
      refine ⟨⟨hyW, hyW'⟩, fun k => ?_⟩
      rcases hy with hy | hy
      · exact mul_eq_zero_of_left ((hSW.le ⟨hy, hyW⟩).2 _) _
      · exact mul_eq_zero_of_right _ ((hTW.le ⟨hy, hyW'⟩).2 _)
    · rintro ⟨⟨hyW, hyW'⟩, h⟩
      refine ⟨?_, hyW, hyW'⟩
      by_cases h0 : ∀ i, f i y = 0
      · exact Or.inl (hSW.ge ⟨hyW, h0⟩).1
      · obtain ⟨i, hi⟩ := not_forall.1 h0
        refine Or.inr (hTW.ge ⟨hyW', fun i' => ?_⟩).1
        have := h (finProdFinEquiv (i, i'))
        simp only [Equiv.symm_apply_apply] at this
        exact (mul_eq_zero.1 this).resolve_left hi

theorem isAnalyticSubset_empty' (A : FinHolAtlas d X) : A.IsAnalyticSubset ∅ := by
  intro x
  refine ⟨Set.univ, isOpen_univ, trivial, 1, fun _ _ => 1, fun _ j => ?_, ?_⟩
  · exact analyticOnNhd_const
  · ext y
    simp

theorem isAnalyticSubset_iUnion {A : FinHolAtlas d X} : ∀ (r : ℕ) (Zs : Fin r → Set X),
    (∀ i, A.IsAnalyticSubset (Zs i)) → A.IsAnalyticSubset (⋃ i, Zs i)
  | 0, Zs, _ => by simpa using isAnalyticSubset_empty' A
  | r + 1, Zs, h => by
    rw [Set.iUnion_fin_add_one_eq_iUnion_succ]
    exact isAnalyticSubset_union (h 0) (isAnalyticSubset_iUnion r _ fun i => h i.succ)

theorem exists_subset_of_subset_iUnion : ∀ (d : ℕ) (X : Type) [TopologicalSpace X]
    (At : FinHolAtlas d X) (C : Set X) (r : ℕ) (Zs : Fin r → Set X),
    IsIrreducibleAnalytic At C → (∀ i, At.IsAnalyticSubset (Zs i)) → C ⊆ ⋃ i, Zs i →
    ∃ i, C ⊆ Zs i := by
  intro d X _ At C r
  induction r with
  | zero =>
    intro Zs hC _ hsub
    obtain ⟨x, hx⟩ := hC.2.1
    simpa using hsub hx
  | succ r ih =>
    intro Zs hC hZ hsub
    rw [Set.iUnion_fin_add_one_eq_iUnion_succ] at hsub
    have hU := isAnalyticSubset_iUnion r (fun i => Zs i.succ) fun i => hZ i.succ
    rcases hC.2.2 _ _ (isAnalyticSubset_inter hC.1 (hZ 0)) (isAnalyticSubset_inter hC.1 hU)
      (by rw [← Set.inter_union_distrib_left]; exact (Set.inter_eq_left.2 hsub).symm) with h | h
    · exact ⟨0, Set.inter_eq_left.1 h.symm⟩
    · obtain ⟨i, hi⟩ := ih (fun i => Zs i.succ) hC (fun i => hZ i.succ) (Set.inter_eq_left.1 h.symm)
      exact ⟨i.succ, hi⟩

end GlobalTheory.AnUnion
