import Formalism.JumpKernelCokernel.Statement

namespace Formalism.KernelCokernelLengths.LengthSplittingLemmas

theorem main (O : Type) [CommRing O] (R : Type) [AddCommGroup R] [Module O R]
    (π : Module.End O R) (R' R'' : Submodule O R) (h : R' ≤ R'') :
    Module.length O (R ⧸ (R' ⊔ LinearMap.range π)) ≤
      Module.length O (R ⧸ (R'' ⊔ LinearMap.range π)) +
        Module.length O (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype) := by
  set A := R' ⊔ LinearMap.range π with hA
  set B := R'' ⊔ LinearMap.range π with hB
  have hAB : A ≤ B := sup_le_sup_right h _
  let f : (B ⧸ A.comap B.subtype) →ₗ[O] (R ⧸ A) := Submodule.mapQ (A.comap B.subtype) A B.subtype le_rfl
  let g : (R ⧸ A) →ₗ[O] (R ⧸ B) := Submodule.mapQ A B LinearMap.id (by simpa using hAB)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mapQ_apply, Submodule.subtype_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hx
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk r, rfl⟩
  have hex : Function.Exact f g := by
    intro y
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero] at hy
      exact ⟨Submodule.Quotient.mk ⟨r, hy⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      simp only [f, g, Submodule.mapQ_apply, Submodule.subtype_apply, LinearMap.id_apply,
        Submodule.Quotient.mk_eq_zero]
      exact b.2
  have hlen := Module.length_eq_add_of_exact f g hf hg hex
  have hRB : R'' ≤ B := le_sup_left
  let k : (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype) →ₗ[O] (B ⧸ A.comap B.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hRB) (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact sup_le_sup_left (LinearMap.map_le_range) R' hx)
  have hk : Function.Surjective k := by
    intro y
    obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨r, hr, p, hp, rfl⟩ := Submodule.mem_sup.mp hb
    refine ⟨Submodule.Quotient.mk ⟨r, hr⟩, ?_⟩
    simp only [k, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion]
    have : r - (r + p) = -p := by abel
    rw [this]
    exact A.neg_mem (Submodule.mem_sup_right hp)
  have hle := Module.length_le_of_surjective k hk
  rw [hlen, add_comm]
  gcongr

end Formalism.KernelCokernelLengths.LengthSplittingLemmas

theorem Formalism.KernelCokernelLengths.length_splits_additively : Formalism.KernelCokernelLengths.LenSplit := by
  intro O _ R _ _ π R' R'' h
  exact Formalism.KernelCokernelLengths.LengthSplittingLemmas.main O R π R' R'' h
