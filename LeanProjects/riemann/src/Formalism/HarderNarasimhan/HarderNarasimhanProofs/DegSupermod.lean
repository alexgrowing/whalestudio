import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ

open Module Submodule

noncomputable section

namespace Formalism.HN

section

variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)

theorem degSupermod_mem_zl (N : Submodule R V) (y : E) :
    y ∈ zl ρ N ↔ ∃ x ∈ N, ρ x = y := Iff.rfl

theorem degSupermod_zl_mono {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (degSupermod_mem_zl ρ A y).mp hy
  exact (degSupermod_mem_zl ρ B _).mpr ⟨x, h hx, rfl⟩

theorem degSupermod_zl_sup (A B : Submodule R V) : zl ρ (A ⊔ B) = zl ρ A ⊔ zl ρ B := by
  simp only [zl, Submodule.sup_toAddSubgroup, AddSubgroup.map_sup]
  first
    | exact SupHomClass.map_sup AddSubgroup.toIntSubmodule _ _
    | (ext y; simp [Submodule.mem_sup, AddSubgroup.mem_sup])

theorem degSupermod_zl_inf {L A B : Submodule R V} (hinj : Set.InjOn ρ (L : Set V))
    (hA : A ≤ L) (hB : B ≤ L) : zl ρ (A ⊓ B) = zl ρ A ⊓ zl ρ B := by
  refine le_antisymm (le_inf (degSupermod_zl_mono ρ inf_le_left)
    (degSupermod_zl_mono ρ inf_le_right)) ?_
  rintro y ⟨hyA, hyB⟩
  obtain ⟨a, ha, rfl⟩ := (degSupermod_mem_zl ρ A y).mp hyA
  obtain ⟨b, hb, hba⟩ := (degSupermod_mem_zl ρ B _).mp hyB

  have hab : b = a := hinj (hB hb) (hA ha) hba
  subst hab
  exact (degSupermod_mem_zl ρ (A ⊓ B) _).mpr ⟨b, ⟨ha, hb⟩, rfl⟩

end

universe u v w in
theorem degSupermod_of (h : DegSupermodZ.{w}) : DegSupermod.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L A B hL hA hB
  haveI := hL.2
  have key := h E (zl ρ L) (zl ρ A) (zl ρ B) hL.2 (degSupermod_zl_mono ρ hA)
    (degSupermod_zl_mono ρ hB)
  rw [← degSupermod_zl_sup ρ A B, ← degSupermod_zl_inf ρ hL.1 hA hB] at key
  exact key

theorem degree_supermodular : DegSupermod := degSupermod_of degree_supermodular_integral

end Formalism.HN
