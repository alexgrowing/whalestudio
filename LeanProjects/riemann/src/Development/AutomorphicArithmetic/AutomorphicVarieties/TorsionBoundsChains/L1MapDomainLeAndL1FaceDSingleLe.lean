import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

private theorem l1_eq_sum {X : Type} (f : X →₀ ℤ) (s : Finset X) (h : f.support ⊆ s) :
    l1 f = ∑ x ∈ s, (f x).natAbs := by
  unfold l1
  exact Finsupp.sum_of_support_subset f h _ (fun _ _ => by simp)

private theorem l1_add_le {X : Type} (f g : X →₀ ℤ) : l1 (f + g) ≤ l1 f + l1 g := by
  classical
  have hs : (f + g).support ⊆ f.support ∪ g.support := Finsupp.support_add
  rw [l1_eq_sum (f + g) _ hs, l1_eq_sum f (f.support ∪ g.support) Finset.subset_union_left,
    l1_eq_sum g (f.support ∪ g.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => by
    simpa using Int.natAbs_add_le (f x) (g x)

private theorem l1_single {X : Type} (x : X) (c : ℤ) : l1 (Finsupp.single x c) = c.natAbs := by
  unfold l1
  exact Finsupp.sum_single_index (by simp)

private theorem l1_sum_le {X ι : Type} (s : Finset ι) (F : ι → X →₀ ℤ) :
    l1 (∑ i ∈ s, F i) ≤ ∑ i ∈ s, l1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (l1_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem UpperTheory.V.KH.l1_mapDomain_le_and_l1_faceD_single_le :
    (∀ (X Y : Type) (φ : X → Y) (f : X →₀ ℤ), l1 (Finsupp.mapDomain φ f) ≤ l1 f) ∧
    (∀ (Y X : Type) (k : ℕ) (face : Fin k → Y → X) (y : Y),
      l1 (faceD face (Finsupp.single y 1)) ≤ k) := by
  refine ⟨fun X Y φ f => ?_, fun Y X k face y => ?_⟩
  · have h : Finsupp.mapDomain φ f = ∑ x ∈ f.support, Finsupp.single (φ x) (f x) := rfl
    rw [h]
    refine (l1_sum_le _ _).trans (le_of_eq ?_)
    simp only [l1_single]
    rfl
  · rw [faceD_single]
    refine (l1_sum_le _ _).trans (le_of_eq ?_)
    simp [Finsupp.smul_single, l1_single, Int.natAbs_pow]
