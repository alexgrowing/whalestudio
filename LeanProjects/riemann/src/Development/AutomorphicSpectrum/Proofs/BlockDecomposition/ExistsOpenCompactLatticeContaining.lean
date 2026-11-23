import Mathlib

open Matrix
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalLattice

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSubgroup (k : Type) [Field k] [ValuativeRel k] (n : ℕ) (γ : ValueGroupWithZero k) :
    AddSubgroup (Fin n → k) where
  carrier := {x | ∀ i, valuation k (x i) ≤ γ}
  zero_mem' := fun i => by simp
  add_mem' := fun {a b} ha hb i =>
    (Valuation.map_add _ _ _).trans (max_le (ha i) (hb i))
  neg_mem' := fun {a} ha i => by simpa using ha i

theorem coe_ballSubgroup (n : ℕ) (γ : ValueGroupWithZero k) :
    (ballSubgroup k n γ : Set (Fin n → k)) =
      Set.univ.pi fun _ => {x : k | valuation k x ≤ γ} := by
  ext x
  simp only [Set.mem_univ_pi, Set.mem_setOf_eq]
  rfl

theorem isCompact_ballSubgroup (n : ℕ) (γ : ValueGroupWithZero k) :
    IsCompact (ballSubgroup k n γ : Set (Fin n → k)) := by
  rw [coe_ballSubgroup]
  exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ

theorem isOpen_ballSubgroup (n : ℕ) {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    IsOpen (ballSubgroup k n γ : Set (Fin n → k)) := by
  refine AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_
  rw [GlobalTheory.CompanionTheory.LocalLattice.coe_ballSubgroup]
  refine set_pi_mem_nhds Set.finite_univ fun i _ => ?_
  exact (IsValuativeTopology.mem_nhds_zero_iff _).2
    ⟨Units.mk0 γ hγ, fun x (hx : valuation k x < γ) => hx.le⟩

theorem exists_compact_open_addSubgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)) (hK : IsCompact K) :
    ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧
      IsOpen (A : Set (Fin n → k)) ∧ K ⊆ A := by
  have hne : ∀ γ : ValueGroupWithZero k, max γ 1 ≠ 0 :=
    fun γ => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right γ 1))
  have hmono : Monotone fun γ : ValueGroupWithZero k =>
      (GlobalTheory.CompanionTheory.LocalLattice.ballSubgroup k n (max γ 1) : Set (Fin n → k)) :=
    fun γ δ hγδ x hx i => (hx i).trans (max_le_max hγδ le_rfl)
  have hcover : K ⊆ ⋃ γ : ValueGroupWithZero k, (GlobalTheory.CompanionTheory.LocalLattice.ballSubgroup k n (max γ 1) : Set (Fin n → k)) := by
    intro x _
    obtain ⟨γ, hγ⟩ := Finite.exists_le fun i => valuation k (x i)
    exact Set.mem_iUnion.2 ⟨γ, fun i => (hγ i).trans (le_max_left γ 1)⟩
  obtain ⟨γ, hγ⟩ := hK.elim_directed_cover _
    (fun γ => GlobalTheory.CompanionTheory.LocalLattice.isOpen_ballSubgroup n (hne γ)) hcover hmono.directed_le
  exact ⟨_, GlobalTheory.CompanionTheory.LocalLattice.isCompact_ballSubgroup n _, GlobalTheory.CompanionTheory.LocalLattice.isOpen_ballSubgroup n (hne γ), hγ⟩

end GlobalTheory.CompanionTheory.LocalLattice
