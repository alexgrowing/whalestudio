import Mathlib

namespace GlobalTheory.ComplementedSup

theorem complemented_sup :
    (let d1 : {K : Type} → [inst : Field K] → {Γ V : Type} → [inst_1 : AddCommGroup V] → [inst_2 : Module K V] → (Γ → V →ₗ[K] V) → Submodule K V → Prop := @(fun {K : Type} [Field K] {Γ V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V) (S : Submodule K V) ↦ ∀ (γ : Γ), ∀ v ∈ S, (f γ : V → V) v ∈ S); let d2 : {K : Type} → [inst : Field K] → {Γ V : Type} → [inst_1 : AddCommGroup V] → [inst_2 : Module K V] → (Γ → V →ₗ[K] V) → Submodule K V → Prop := @(fun {K : Type} [Field K] {Γ V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V) (Y : Submodule K V) ↦ ∀ (W : Submodule K V), d1 f W → W ≤ Y → ∃ (C : Submodule K V), d1 f C ∧ C ≤ Y ∧ W ⊓ C = ⊥ ∧ W ⊔ C = Y); ∀ {K : Type} [inst : Field K] {Γ V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module K V] {f : Γ → V →ₗ[K] V} {X U : Submodule K V}, d1 f X → d1 f U → d2 f X → d2 f U → d2 f (X ⊔ U)) := by
  intro d1 d2 K _ Γ V _ _ f X U hX hU hXc hUc

  have hsup : ∀ A B : Submodule K V, d1 f A → d1 f B → d1 f (A ⊔ B) := by
    intro A B hA hB γ v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (hA γ a ha) (hB γ b hb)
  have hinf : ∀ A B : Submodule K V, d1 f A → d1 f B → d1 f (A ⊓ B) := by
    intro A B hA hB γ v hv
    exact Submodule.mem_inf.mpr ⟨hA γ v (Submodule.mem_inf.mp hv).1, hB γ v (Submodule.mem_inf.mp hv).2⟩
  intro W hW hWle

  obtain ⟨D, hD, hDX, hD1, hD2⟩ := hXc (W ⊓ X) (hinf W X hW hX) inf_le_right
  obtain ⟨B, hB, hBU, hB1, hB2⟩ := hUc ((W ⊔ X) ⊓ U) (hinf _ U (hsup W X hW hX) hU) inf_le_right
  refine ⟨D ⊔ B, hsup D B hD hB, sup_le_sup hDX hBU, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwW, hwDB⟩ := Submodule.mem_inf.mp hw
    obtain ⟨d, hd, b, hb, rfl⟩ := Submodule.mem_sup.mp hwDB
    have hbA : b ∈ (W ⊔ X) ⊓ U := by
      refine Submodule.mem_inf.mpr ⟨?_, hBU hb⟩
      have hbd : b = (d + b) - d := by abel
      rw [hbd]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hwW) (Submodule.mem_sup_right (hDX hd))
    have hb0 : b = 0 := by
      have hb' : b ∈ (W ⊔ X) ⊓ U ⊓ B := Submodule.mem_inf.mpr ⟨hbA, hb⟩
      rw [hB1] at hb'
      exact (Submodule.mem_bot K).mp hb'
    subst hb0
    rw [add_zero] at hwW ⊢
    have hd' : d ∈ W ⊓ X ⊓ D := Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hwW, hDX hd⟩, hd⟩
    rw [hD1] at hd'
    exact hd'
  · apply le_antisymm
    · exact sup_le hWle (sup_le_sup hDX hBU)
    · have hX' : X ≤ W ⊔ (D ⊔ B) := by
        rw [← hD2]
        exact sup_le (le_trans inf_le_left le_sup_left) (le_trans le_sup_left le_sup_right)
      have hU' : U ≤ W ⊔ (D ⊔ B) := by
        rw [← hB2]
        exact sup_le (le_trans inf_le_left (sup_le le_sup_left hX')) (le_trans le_sup_right le_sup_right)
      exact sup_le hX' hU'

end GlobalTheory.ComplementedSup
