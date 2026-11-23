import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin

noncomputable section

open Module Submodule

namespace GlobalTheory

section General

variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {N : V → ℝ} {S : Set V} {n : ℕ}

theorem mem_span_of_lt_succMinOf {v : Fin n → V} (hv : LinearIndependent K v) (hS : ∀ j, v j ∈ S)
    (hN : ∀ j : Fin n, N (v j) ≤ succMinOf K N S (j + 1)) {i : ℕ} (hi : i ≤ n) {x : V}
    (hx : x ∈ S) (hx0 : 0 ≤ N x) (h : N x < succMinOf K N S (i + 1)) :
    x ∈ span K (v '' {j | (j : ℕ) < i}) := by
  have hrank : (n : Cardinal) ≤ Module.rank K (span K S) :=
    natCast_le_rank_span_iff.2 ⟨v, hv, hS⟩
  have key : ∀ i ≤ n, succMinOf K N S i ≤ N x → N x < succMinOf K N S (i + 1) →
      x ∈ span K (v '' {j | (j : ℕ) < i}) := by
    intro i hi h1 h2
    by_contra hx'
    have hw : LinearIndependent K (fun j : Fin i => v (Fin.castLE hi j)) :=
      hv.comp _ (Fin.castLE_injective hi)
    have hr : Set.range (fun j : Fin i => v (Fin.castLE hi j)) = v '' {j | (j : ℕ) < i} := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨_, j.2, rfl⟩
      · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
    have hli : LinearIndependent K
        (Fin.cons x (fun j : Fin i => v (Fin.castLE hi j)) : Fin (i + 1) → V) :=
      linearIndependent_finCons.2 ⟨hw, by rwa [hr]⟩
    refine absurd (succMinOf_le_of_linearIndependent (N := N) (S := S) (i := i + 1) hli (by simp)
      hx0 ?_ ?_) (not_le.2 h2)
    · intro k
      refine Fin.cases hx (fun j => hS _) k
    · intro k
      refine Fin.cases le_rfl (fun j => ?_) k
      exact (hN _).trans ((succMinOf_mono (show (j : ℕ) + 1 ≤ i from j.2)
        ((Nat.cast_le.2 hi).trans hrank)).trans h1)
  induction i with
  | zero => exact key 0 hi (succMinOf_zero.le.trans hx0) h
  | succ m ih =>
    rcases lt_or_ge (N x) (succMinOf K N S (m + 1)) with h1 | h1
    · have hsub : {j : Fin n | (j : ℕ) < m} ⊆ {j : Fin n | (j : ℕ) < m + 1} :=
        fun j hj => Nat.lt_succ_of_lt hj
      exact span_mono (Set.image_mono hsub) (ih (Nat.le_of_succ_le hi) h1)
    · exact key (m + 1) hi h1 h

theorem exists_linearIndependent_eq_succMinOf (hfin : ∀ R, {x | x ∈ S ∧ N x ≤ R}.Finite)
    (hN : ∀ x ∈ S, 0 ≤ N x) (hn : (n : Cardinal) ≤ Module.rank K (span K S)) :
    ∃ v : Fin n → V, LinearIndependent K v ∧ (∀ j, v j ∈ S) ∧
      ∀ j : Fin n, N (v j) = succMinOf K N S (j + 1) := by
  induction n with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0, fun j => j.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv, hS, hvN⟩ := ih ((Nat.cast_le.2 (Nat.le_succ m)).trans hn)
    obtain ⟨-, w, hw, hwS⟩ := mem_succMinRadii_iff.1 (succMinOf_mem hfin hn)
    obtain ⟨k, hk⟩ : ∃ k, w k ∉ span K (Set.range v) := by
      by_contra! h
      have h1 : span K (Set.range w) ≤ span K (Set.range v) :=
        span_le.2 (Set.range_subset_iff.2 h)
      have : Module.Finite K (span K (Set.range v)) :=
        Module.Finite.span_of_finite K (Set.finite_range v)
      have h2 := Submodule.finrank_mono h1
      rw [finrank_span_eq_card hw, finrank_span_eq_card hv] at h2
      simp at h2
    have hk' : N (w k) = succMinOf K N S (m + 1) := by
      refine le_antisymm (hwS k).2 (not_lt.1 fun h => hk ?_)
      exact span_mono (Set.image_subset_range _ _)
        (mem_span_of_lt_succMinOf hv hS (fun j => (hvN j).le) le_rfl (hwS k).1
          (hN _ (hwS k).1) h)
    refine ⟨Fin.snoc v (w k), linearIndependent_finSnoc.2 ⟨hv, hk⟩, fun j => ?_, fun j => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using (hwS k).1
      · simpa using hS j
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hk'
      · simpa using hvN j

end General

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {n : ℕ}

theorem mem_span_of_norm_lt_succMin {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (hL : ∀ j, v j ∈ L) (hN : ∀ j : Fin n, ‖v j‖ ≤ succMin L (j + 1)) {i : ℕ} (hi : i ≤ n) {x : E}
    (hx : x ∈ L) (h : ‖x‖ < succMin L (i + 1)) : x ∈ span ℝ (v '' {j | (j : ℕ) < i}) :=
  mem_span_of_lt_succMinOf (N := fun x : E => ‖x‖) (S := (L : Set E)) hv hL hN hi hx
    (norm_nonneg x) h

theorem succMin_le_norm_of_notMem_span {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (hL : ∀ j, v j ∈ L) (hN : ∀ j : Fin n, ‖v j‖ ≤ succMin L (j + 1)) {i : ℕ} (hi : i ≤ n) {x : E}
    (hx : x ∈ L) (h : x ∉ span ℝ (v '' {j | (j : ℕ) < i})) : succMin L (i + 1) ≤ ‖x‖ :=
  not_lt.1 fun h' => h (mem_span_of_norm_lt_succMin hv hL hN hi hx h')

variable [FiniteDimensional ℝ E] [DiscreteTopology L]

theorem exists_linearIndependent_norm_eq_succMin (hn : n ≤ finrank ℝ (span ℝ (L : Set E))) :
    ∃ v : Fin n → E, LinearIndependent ℝ v ∧ (∀ j, v j ∈ L) ∧
      ∀ j : Fin n, ‖v j‖ = succMin L (j + 1) :=
  exists_linearIndependent_eq_succMinOf (N := fun x : E => ‖x‖) (S := (L : Set E))
    (finite_mem_and_norm_le L) (fun x _ => norm_nonneg x) (natCast_le_rank_of_le_finrank hn)

variable (L) [IsZLattice ℝ L]

theorem exists_basis_norm_eq_succMin :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, (∀ j, b j ∈ L) ∧
      ∀ j : Fin (finrank ℝ E), ‖b j‖ = succMin L (j + 1) := by
  obtain ⟨v, hv, hL, hN⟩ :=
    exists_linearIndependent_norm_eq_succMin (L := L) (finrank_span_of_isZLattice L).ge
  have htop : ⊤ ≤ span ℝ (Set.range v) := by
    rw [top_le_iff]
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  exact ⟨Basis.mk hv htop, by simpa using hL, by simpa using hN⟩

end Normed

section Quadratic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V} {L : Submodule ℤ V}
  {n : ℕ}

end Quadratic

end GlobalTheory
