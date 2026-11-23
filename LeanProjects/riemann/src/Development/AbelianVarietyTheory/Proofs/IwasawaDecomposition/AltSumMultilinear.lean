import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.PolarMultilinear

theorem powerset_map {α β : Type} (f : α → β) (s : Multiset α) :
    (s.map f).powerset = s.powerset.map (Multiset.map f) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.powerset_cons, ih, Multiset.map_map]

theorem powerset_val {α : Type} (s : Finset α) :
    s.val.powerset = s.powerset.val.map Finset.val := by
  simp [Finset.powerset, Multiset.map_pmap, Multiset.pmap_eq_map]

theorem alt_sum {d : ℕ} (r : Fin d → Fin d) :
    (∑ T : Finset (Fin d), if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) =
      if Function.Surjective r then 1 else 0 := by
  classical
  have h := Finset.prod_add (fun _ : Fin d => (1 : ℝ))
    (fun j : Fin d => if j ∈ Set.range r then (0 : ℝ) else -1) Finset.univ
  rw [Finset.powerset_univ] at h
  have h2 : ∀ T : Finset (Fin d), (if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) =
      (∏ _i ∈ T, (1 : ℝ)) * ∏ j ∈ Finset.univ \ T, (if j ∈ Set.range r then (0 : ℝ) else -1) := by
    intro T
    rw [Finset.prod_const_one, one_mul]
    split_ifs with hT
    · rw [Finset.prod_congr rfl (g := fun _ => (-1 : ℝ)), Finset.prod_const, Finset.card_univ_diff,
        Fintype.card_fin]
      intro j hj
      rw [if_neg]
      rintro ⟨i, rfl⟩
      exact (Finset.mem_sdiff.1 hj).2 (hT i)
    · obtain ⟨i, hi⟩ := not_forall.1 hT
      exact (Finset.prod_eq_zero (i := r i) (by simp [hi]) (by simp)).symm
  rw [Finset.sum_congr rfl fun T _ => h2 T, ← h]
  split_ifs with hs
  · refine Finset.prod_eq_one fun j _ => ?_
    rw [if_pos (show j ∈ Set.range r from hs j), add_zero]
  · obtain ⟨j, hj⟩ := not_forall.1 hs
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [if_neg (show ¬ j ∈ Set.range r from hj)]; ring

theorem alt_sum_multilinear {A : Type} [AddCommGroup A] {d : ℕ}
    (M : MultilinearMap ℤ (fun _ : Fin d => A) ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin d)) (a : Fin d → A), M (a ∘ σ) = M a) (a : Fin d → A) :
    (∑ T : Finset (Fin d), (-1 : ℝ) ^ (d - T.card) * M fun _ => ∑ i ∈ T, a i) =
      (d.factorial : ℝ) * M a := by
  classical
  have h1 : ∀ T : Finset (Fin d), (-1 : ℝ) ^ (d - T.card) * (M fun _ => ∑ i ∈ T, a i) =
      ∑ r : Fin d → Fin d, (if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) * M (a ∘ r) := by
    intro T
    rw [M.map_sum_finset (fun _ i => a i) (fun _ => T), Finset.mul_sum]
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun r _ => rfl
    ext r
    simp [Fintype.mem_piFinset]
  rw [Finset.sum_congr rfl fun T _ => h1 T, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, alt_sum, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have h3 : (∑ r ∈ Finset.univ.filter (fun r : Fin d → Fin d => Function.Surjective r), M (a ∘ r)) =
      ∑ σ : Equiv.Perm (Fin d), M (a ∘ σ) := by
    symm
    refine Finset.sum_bij (fun σ _ => (σ : Fin d → Fin d)) ?_ ?_ ?_ ?_
    · intro σ _
      simpa using σ.surjective
    · intro σ _ τ _ h
      exact Equiv.ext (congrFun h)
    · intro r hr
      have hs : Function.Surjective r := by simpa using hr
      exact ⟨Equiv.ofBijective r (Finite.surjective_iff_bijective.1 hs), Finset.mem_univ _, rfl⟩
    · intro σ _
      rfl
  rw [h3]
  simp [hM, Fintype.card_perm]

theorem polar_diag : ∀ (A : Type) [AddCommGroup A] (d : ℕ) (M : MultilinearMap ℤ (fun _ : Fin d => A) ℝ),
    (∀ (σ : Equiv.Perm (Fin d)) (a : Fin d → A), M (a ∘ σ) = M a) →
    ∀ a : Fin d → A, polar (fun b => M fun _ => b) (Multiset.map a Finset.univ.val) = M a := by
  intro A _ d M hM a
  have hc : Multiset.card (Multiset.map a Finset.univ.val) = d := by simp
  unfold Pad.polar
  rw [hc, powerset_map, powerset_val, Multiset.map_map, Multiset.map_map, Finset.powerset_univ]
  have h := alt_sum_multilinear M hM a
  have h' : (Multiset.map (((fun T : Multiset A => (-1 : ℝ) ^ (d - Multiset.card T) * M fun _ => T.sum) ∘
      Multiset.map a) ∘ Finset.val) (Finset.univ : Finset (Finset (Fin d))).val).sum =
      (d.factorial : ℝ) * M a := by
    rw [← h, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun T _ => ?_
    simp only [Function.comp, Multiset.card_map, Finset.card_val]
    rfl
  rw [h', ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast d.factorial_ne_zero), one_mul]

end GlobalTheory.ShFam.PolarMultilinear
