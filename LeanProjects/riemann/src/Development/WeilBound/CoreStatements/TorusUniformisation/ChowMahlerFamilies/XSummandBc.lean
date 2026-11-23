import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
open GlobalTheory.CompanionTheory.Ar.Num

theorem PositivityTheory.Xgn.t_summand_bc : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] (b : V →ₗ[Ω] Vc), IsBaseChange C b → ∀ (L : AddSubgroup V) (U : Submodule Ω V), (∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) → Summand L U → Summand (spanOver RC (b '' L)) (Submodule.span C (b '' U)) ∧ spanOver RC (b '' L) ⊓ (Submodule.span C (b '' U)).toAddSubgroup = spanOver RC (b '' (L ⊓ U.toAddSubgroup : AddSubgroup V)) := by
  intro o Ω C _ _ _ _ _ _ _ R RC hR V Vc _ _ _ _ _ _ b hb L U hL hS
  obtain ⟨ρ, hρU, hρid, hρL⟩ := hS
  let ρC : Vc →ₗ[C] Vc := hb.lift (b ∘ₗ ρ)
  have hρC : ∀ v, ρC (b v) = b (ρ v) := fun v => hb.lift_eq _ v
  have hmap : ∀ {S T : Set V}, (∀ e ∈ S, ρ e ∈ T) →
      ∀ x ∈ spanOver RC (b '' S), ρC x ∈ spanOver RC (b '' T) := by
    intro S T hST x hx
    unfold spanOver at hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hy
      rw [map_smul, hρC]
      exact AddSubgroup.subset_closure ⟨a, ha, _, ⟨ρ e, hST e he, rfl⟩, rfl⟩
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      rw [map_add]
      exact add_mem hy hz
    | neg y _ hy =>
      rw [map_neg]
      exact neg_mem hy
  have hid : ∀ u ∈ Submodule.span C (b '' U), ρC u = u := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, rfl⟩ := hx
      rw [hρC, hρid e he]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  refine ⟨⟨ρC, fun v => ?_, hid, hmap hρL⟩, ?_⟩
  · refine hb.inductionOn v (fun v => ρC v ∈ Submodule.span C (b '' U)) ?_ ?_ ?_ ?_
    · show ρC 0 ∈ _
      rw [map_zero]
      exact zero_mem _
    · intro m
      show ρC (b m) ∈ _
      rw [hρC]
      exact Submodule.subset_span ⟨ρ m, hρU m, rfl⟩
    · intro s n hn
      show ρC (s • n) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ s hn
    · intro n₁ n₂ h₁ h₂
      show ρC (n₁ + n₂) ∈ _
      rw [map_add]
      exact add_mem h₁ h₂
  · apply le_antisymm
    · rintro x ⟨hx1, hx2⟩
      rw [← hid x hx2]
      exact hmap (S := (L : Set V)) (T := ((L ⊓ U.toAddSubgroup : AddSubgroup V) : Set V))
        (fun e he => ⟨hρL e he, hρU e⟩) x hx1
    · apply (AddSubgroup.closure_le _).2
      rintro _ ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
      constructor
      · exact AddSubgroup.subset_closure ⟨a, ha, _, ⟨e, he.1, rfl⟩, rfl⟩
      · exact Submodule.smul_mem _ a (Submodule.subset_span ⟨e, he.2, rfl⟩)
