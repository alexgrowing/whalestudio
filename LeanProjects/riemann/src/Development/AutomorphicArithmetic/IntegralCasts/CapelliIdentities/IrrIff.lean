import Mathlib

theorem UpperTheory.Reformulated.B.Ra6.irr_iff :
    ∀ {G W : Type} [inst : Group G] [inst_1 : AddCommGroup W]
    [inst_2 : _root_.Module ℂ W] (ρ : Representation ℂ G W),
    ρ.IsIrreducible ↔
      Nontrivial W ∧
        ∀ (N : Submodule ℂ W), (∀ (g : G), ∀ v ∈ N, ((ρ : G → W →ₗ[ℂ] W) g : W → W) v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro G W _ _ _ ρ
  constructor
  · intro h
    have h' : IsSimpleOrder (Subrepresentation ρ) := h
    refine ⟨?_, fun N hN => ?_⟩
    · have hne : (⊥ : Submodule ℂ W) ≠ ⊤ := fun e =>
        (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)
      exact (Submodule.nontrivial_iff ℂ).mp ⟨⊥, ⊤, hne⟩
    · rcases h'.eq_bot_or_eq_top ⟨N, fun g v hv => hN g v hv⟩ with e | e
      · exact Or.inl (congrArg Subrepresentation.toSubmodule e)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule e)
  · rintro ⟨hW, h⟩
    have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun e =>
      (bot_ne_top (α := Submodule ℂ W)) (congrArg Subrepresentation.toSubmodule e)
    have h' : IsSimpleOrder (Subrepresentation ρ) :=
      { exists_pair_ne := ⟨⊥, ⊤, hne⟩
        eq_bot_or_eq_top := fun σ =>
          (h σ.toSubmodule fun g v hv => σ.apply_mem_toSubmodule g hv).imp
            (fun e => Subrepresentation.toSubmodule_injective e)
            (fun e => Subrepresentation.toSubmodule_injective e) }
    exact h'
