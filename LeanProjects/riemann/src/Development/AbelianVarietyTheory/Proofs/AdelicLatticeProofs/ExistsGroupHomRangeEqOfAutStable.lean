import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem IsPre.exists_group_range :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ →
      ∃ (G : Type) (_ : Group G) (ρ : G →* Matrix ι ι ℂ), Set.range ρ = Γ := by
  intro ι _ _ Γ hΓ
  let H : Subgroup (Matrix.SpecialLinearGroup ι ℂ) :=
    { carrier := {g | (g : Matrix ι ι ℂ) ∈ Γ}
      one_mem' := hΓ.one_mem
      mul_mem' := fun {a b} ha hb => hΓ.mul_mem _ ha _ hb
      inv_mem' := fun {a} ha => hΓ.adj_mem _ ha }
  let ρ : H →* Matrix ι ι ℂ :=
    { toFun := fun g => ((g : Matrix.SpecialLinearGroup ι ℂ) : Matrix ι ι ℂ)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨H, inferInstance, ρ, ?_⟩
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hg
    exact ⟨⟨⟨g, hΓ.det_eq g hg⟩, hg⟩, rfl⟩

end GlobalTheory.ClassFin
