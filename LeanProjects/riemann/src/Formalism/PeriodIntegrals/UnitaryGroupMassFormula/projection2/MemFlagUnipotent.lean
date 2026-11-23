import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Assemble

noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

variable {k : Type} [Field k] {n c : ℕ}

private theorem symm_mem_Ufl_of_maps_Ufl {i : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)}
    (h : ∀ v ∈ PI.OneCosetSharp.Loc.Ufl k n c i, r v ∈ PI.OneCosetSharp.Loc.Ufl k n c i) {v : Fin (n + c) → k}
    (hv : v ∈ PI.OneCosetSharp.Loc.Ufl k n c i) : r.symm v ∈ PI.OneCosetSharp.Loc.Ufl k n c i := by
  have hle : (PI.OneCosetSharp.Loc.Ufl k n c i).map (r : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k)) ≤ PI.OneCosetSharp.Loc.Ufl k n c i := by
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  have heq : (PI.OneCosetSharp.Loc.Ufl k n c i).map (r : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k)) = PI.OneCosetSharp.Loc.Ufl k n c i :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq r _)
  rw [← heq] at hv
  obtain ⟨w, hw, hwv⟩ := hv
  have : r.symm v = w := by
    rw [LinearEquiv.symm_apply_eq]
    exact hwv.symm
  rw [this]
  exact hw

theorem R1cond_symm {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) : R1cond k n c r.symm := by
  obtain ⟨h1, h2, h3⟩ := hr
  refine ⟨fun i v hv => symm_mem_Ufl_of_maps_Ufl (h1 i) hv, ?_, fun i => ?_⟩
  · rw [LinearEquiv.symm_apply_eq]
    exact h2.symm
  · have hu := symm_mem_Ufl_of_maps_Ufl (h1 i) (h3 i)
    have hneg := (PI.OneCosetSharp.Loc.Ufl k n c i).neg_mem hu
    have : r.symm (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i) =
        -r.symm (r (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) := by
      rw [map_sub, LinearEquiv.symm_apply_apply, neg_sub]
    rw [this]
    exact hneg

theorem mem_flagUnipotent {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) : r ∈ R1 k n c :=
  ⟨hr, R1cond_symm hr⟩

theorem mem_Ufl {i : ℕ} {v : Fin (n + c) → k} : v ∈ Ufl k n c i ↔ ∀ l : Fin (n + c), n + i ≤ l.1 → v l = 0 := by
  show (∀ l : Fin (n + c), l.1 ∉ {l | l < n + i} → v l = 0) ↔ _
  simp only [Set.mem_ofPred_eq, not_lt]

def XP : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if l.1 < n then LinearMap.proj l else 0

def AP : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if l.1 < n then 0 else LinearMap.proj l

theorem lowProj_apply₂ (v : Fin (n + c) → k) (l : Fin (n + c)) : (XP : (Fin (n + c) → k) →ₗ[k] _) v l = if l.1 < n then v l else 0 := by
  by_cases h : l.1 < n <;> simp [XP, h]

theorem projA_apply (v : Fin (n + c) → k) (l : Fin (n + c)) : (AP : (Fin (n + c) → k) →ₗ[k] _) v l = if l.1 < n then 0 else v l := by
  by_cases h : l.1 < n <;> simp [AP, h]

theorem lowProj_add_highProj (v : Fin (n + c) → k) : (XP : (Fin (n + c) → k) →ₗ[k] _) v + AP v = v := by
  funext l
  rw [Pi.add_apply, lowProj_apply₂, projA_apply]
  by_cases h : l.1 < n <;> simp [h]

theorem projA_inX (v : Fin n → k) : (AP : (Fin (n + c) → k) →ₗ[k] _) (inX k n c v) = 0 := by
  funext l
  rw [projA_apply]
  by_cases h : l.1 < n
  · simp [h]
  · simp [h, PI.OneCosetSharp.Loc.inX]

end PI.OneCosetSharp.W
