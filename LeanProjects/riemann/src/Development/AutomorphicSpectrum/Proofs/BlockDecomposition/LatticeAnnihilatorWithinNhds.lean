import Mathlib

open Matrix ValuativeRel
open scoped Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.AnnihShrink

theorem exists_ne_zero_valuation_lt (k : Type) [Field k] [ValuativeRel k] [ValuativeRel.IsNontrivial k]
    (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) : ∃ t : k, t ≠ 0 ∧ valuation k t < γ := by
  obtain ⟨γ₀, h0, h1⟩ := ValuativeRel.IsNontrivial.condition (R := k)
  obtain ⟨ε, hε0, hε1⟩ : ∃ ε : ValueGroupWithZero k, ε ≠ 0 ∧ ε < 1 := by
    rcases lt_or_gt_of_ne h1 with h | h
    · exact ⟨γ₀, h0, h⟩
    · exact ⟨γ₀⁻¹, inv_ne_zero h0, inv_lt_one_of_one_lt₀ h⟩
  obtain ⟨t, ht⟩ := valuation_surjective (K := k) (ε * γ)
  have hpos : 0 < γ := zero_lt_iff.mpr hγ
  refine ⟨t, ?_, ?_⟩
  · rw [← (valuation k).ne_zero_iff, ht]
    exact mul_ne_zero hε0 hγ
  · rw [ht]
    exact mul_lt_of_lt_one_left hpos hε1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (n : ℕ) (b : k) : AddSubgroup (Fin n → k) where
  carrier := {a | ∀ j, valuation k (a j) ≤ valuation k b}
  zero_mem' := fun j => by simp
  add_mem' := fun {x y} hx hy j =>
    ((valuation k).map_add _ _).trans (max_le (hx j) (hy j))
  neg_mem' := fun {x} hx j => by simpa using hx j

theorem isCompact_box (n : ℕ) (b : k) : IsCompact (box n b : Set (Fin n → k)) := by
  have : (box n b : Set (Fin n → k)) =
      Set.univ.pi (fun _ => {y : k | valuation k y ≤ valuation k b}) := by
    ext a
    exact ⟨fun h j _ => h j, fun h j => h j (Set.mem_univ j)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _

theorem isOpen_box (n : ℕ) (b : k) (hb : b ≠ 0) : IsOpen (box n b : Set (Fin n → k)) := by
  have hvb : valuation k b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  have hU : Set.univ.pi (fun _ : Fin n => {y : k | valuation k y < valuation k b}) ∈
      nhds (0 : Fin n → k) :=
    set_pi_mem_nhds Set.finite_univ fun j _ =>
      (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hvb
  refine (box n b).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset hU ?_)
  intro x hx j
  exact (hx j (Set.mem_univ j)).le

theorem exists_compact_open_annihilator_subset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (U : Set (Fin n → k)),
      U ∈ nhds (0 : Fin n → k) → ∃ A : AddSubgroup (Fin n → k),
        IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧
        {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ⊆ U := by
  intro k _ _ _ _ ψ _ hne n U hU
  obtain ⟨y₀, hy⟩ : ∃ y : k, ψ y ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne (AddChar.ext _ _ fun t => by simpa using hall t)
  have hy0 : y₀ ≠ 0 := by
    rintro rfl
    exact hy (by simp)

  obtain ⟨I, V, hV, hIV⟩ : ∃ (I : Set (Fin n)) (V : Fin n → Set k),
      (∀ i, V i ∈ nhds (0 : k)) ∧ I.pi V ⊆ U := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, _, V, hV, hIV⟩ := hU
    exact ⟨I, V, hV, hIV⟩
  have hball : ∀ i, ∃ γ : (ValueGroupWithZero k)ˣ, {y : k | valuation k y < γ} ⊆ V i := fun i =>
    (IsValuativeTopology.mem_nhds_zero_iff (V i)).1 (hV i)
  choose g hg using hball
  obtain ⟨γ, hγ0, hγ⟩ : ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ i, γ ≤ (g i : ValueGroupWithZero k) := by
    obtain ⟨m, hm⟩ := Finite.exists_ge g
    exact ⟨m, m.ne_zero, fun i => Units.val_le_val.2 (hm i)⟩
  obtain ⟨t, ht0, ht⟩ := exists_ne_zero_valuation_lt k γ hγ0
  refine ⟨box n (y₀ / t), isCompact_box n _, isOpen_box n _ (div_ne_zero hy0 ht0), ?_⟩
  intro ξ hξ
  apply hIV
  intro i _
  apply hg i
  show valuation k (ξ i) < g i
  refine lt_of_lt_of_le ?_ (hγ i)
  by_contra hlt
  have hle : γ ≤ valuation k (ξ i) := not_lt.mp hlt
  have hvξ : valuation k (ξ i) ≠ 0 := (lt_of_lt_of_le (zero_lt_iff.mpr hγ0) hle).ne'
  have hξi : ξ i ≠ 0 := (Valuation.ne_zero_iff _).1 hvξ
  have hmem : (Pi.single i (y₀ / ξ i) : Fin n → k) ∈ box n (y₀ / t) := by
    intro j
    by_cases h : j = i
    · subst h
      have he : y₀ / ξ j = (y₀ / t) * (t / ξ j) := by field_simp
      rw [Pi.single_eq_same, he, map_mul]
      refine mul_le_of_le_one_right' ?_
      rw [map_div₀]
      exact (div_le_one₀ (zero_lt_iff.mpr hvξ)).2 (ht.le.trans hle)
    · simp [Pi.single_eq_of_ne h]
  have h1 := hξ _ hmem
  rw [dotProduct_single, mul_div_cancel₀ _ hξi] at h1
  exact hy h1

end GlobalTheory.CompanionTheory.AnnihShrink
