import Mathlib

noncomputable def UpperTheory.Reformulated.B.SchurIrreducible.Irr :
    {G : Type} → [inst : Group G] → {N : ℕ} → (G →* GL (Fin N) ℂ) → Prop :=
    fun {G : Type} [Group G] {N : ℕ} (ρ : G →* GL (Fin N) ℂ) ↦
      ∀ (S : Submodule ℂ (Fin N → ℂ)),
        (∀ (g : G), ∀ v ∈ S, (↑((ρ : G → GL (Fin N) ℂ) g) : Matrix (Fin N) (Fin N) ℂ).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤

noncomputable def UpperTheory.Reformulated.B.SchurIrreducible.SchurStep :
    Prop :=
    ∀ (G : Type) [inst : Group G] (M : ℕ) (σ : G →* GL (Fin M) ℂ),
      UpperTheory.Reformulated.B.SchurIrreducible.Irr σ →
        ∀ (C : Matrix (Fin M) (Fin M) ℂ),
          (∀ (g : G),
              (↑((σ : G → GL (Fin M) ℂ) g) : Matrix (Fin M) (Fin M) ℂ) * C =
                C * (↑((σ : G → GL (Fin M) ℂ) g) : Matrix (Fin M) (Fin M) ℂ)) →
            ∃ (c : ℂ), C = c • (1 : Matrix (Fin M) (Fin M) ℂ)

theorem UpperTheory.Reformulated.B.SchurIrreducible.schurStep :
    UpperTheory.Reformulated.B.SchurIrreducible.SchurStep := by
  intro G _ M σ hσ C hC
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact ⟨0, Subsingleton.elim _ _⟩
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' C)
  refine ⟨c, ?_⟩
  have hS := hσ (Module.End.eigenspace (Matrix.toLin' C) c) (by
    intro g v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hC g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul])
  rcases hS with h | h
  · exact absurd h hc
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' C) c := by
      rw [h]; exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]
    simp
