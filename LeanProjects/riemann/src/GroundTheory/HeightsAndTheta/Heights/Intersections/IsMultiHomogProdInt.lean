import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverChart
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GenericPointsAvoidBadLocus

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K] in

theorem isMultiHomog_prod_int {β : Type*} (s : Finset β) (f : β → MRing ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m hm k
    rw [Finset.prod_empty, MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    intro m hm k
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    have h1 := h b (Finset.mem_insert_self b s) m1 hm1 k
    have h2 := ih (fun b' hb' => h b' (Finset.mem_insert_of_mem hb')) m2 hm2 k
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, h1, h2]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem adjoin_chart_le {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
    (G : GenFibre v P') (i j : ∀ k : FibreBlock κ, ι' k.1) (hi : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0) :
    IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) ≤
      IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨q, rfl⟩
  have hq : G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩ =
      (G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) / (G.x' ⟨q.1.1, j q.1⟩ / G.x' ⟨q.1.1, i q.1⟩) :=
    (div_div_div_cancel_right₀ (hi q.1) _ _).symm
  show G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩ ∈ _
  rw [hq]
  exact div_mem (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩)
    (IntermediateField.subset_adjoin _ _ ⟨⟨q.1, j q.1⟩, rfl⟩)

end GenericPointsAvoidBadLocus

open GenericPointsAvoidBadLocus in

theorem GenericPointsAvoidBadLocus.proof (hChart : GenericPointsInAffineChart.Statement) : GenericPointsAvoidBadLocus.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G i hv hP' hZ hi
  classical
  let C := {j : ∀ k : FibreBlock κ, ι' k.1 // ∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0}
  choose D a hD hDZ hpts using fun j : C => hChart K ι K' ι' κ v P' n G j.1 hv hP' hZ j.2
  have hprime : (imageZ v P').IsPrime := hZ.2.1.1
  refine ⟨∏ j, D j, ∑ j, a j, isMultiHomog_prod_int _ _ _ fun j _ => hD j, fun hmem => ?_, ?_⟩
  · obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hDZ j hj
  intro z hz hDz
  have hDj : ∀ j : C, eval z (map (Int.castRingHom ℂ) (D j)) ≠ 0 := by
    intro j h0
    apply hDz
    rw [map_prod, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) h0
  let i0 : C := ⟨i, hi⟩
  have hEq : ∀ j : C, ptsOverChart P' κ v i z = ptsOverChart P' κ v j.1 z := by
    intro j
    have hci : (ptsOverChart P' κ v i z).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩)) :=
      (hpts i0 z hz (hDj i0)).2.1
    obtain ⟨hfin, hcj, -⟩ := hpts j z hz (hDj j)
    have hsub : ptsOverChart P' κ v i z ⊆ ptsOverChart P' κ v j.1 z := by
      rintro O ⟨z', hz', rfl, hw, hc⟩
      exact ⟨z', hz', rfl, hw, fun k => (hpts i0 z hz (hDj i0)).2.2 z' hz' hw hc ⟨k, j.1 k⟩ (j.2 k)⟩
    refine Set.eq_of_subset_of_ncard_le hsub (le_of_eq ?_) hfin
    rw [hcj, hci, le_antisymm (adjoin_chart_le G i j.1 hi) (adjoin_chart_le G j.1 i j.2)]
  have hall : ptsOverPt P' v z = ptsOverChart P' κ v i z := by
    ext O
    constructor
    · rintro ⟨z', hz', rfl, hw⟩
      choose ℓ hℓ using fun k : FibreBlock κ => hz'.1 k.1
      have hgen : ∀ k : FibreBlock κ, G.x' ⟨k.1, ℓ k⟩ ≠ 0 := by
        intro k h0
        apply hℓ k
        have hmem : (X ⟨k.1, ℓ k⟩ : MRing ι') ∈ P' := by
          rw [← G.genericFibre_ker_target, RingHom.mem_ker]
          simpa using h0
        simpa using hz'.2 _ hmem
      rw [hEq ⟨ℓ, hgen⟩]
      exact ⟨z', hz', rfl, hw, hℓ⟩
    · rintro ⟨z', hz', rfl, hw, -⟩
      exact ⟨z', hz', rfl, hw⟩
  rw [hall]
  exact (hpts i0 z hz (hDj i0)).2.1

end GroundTheory.Heights₂.Heights.Inter
