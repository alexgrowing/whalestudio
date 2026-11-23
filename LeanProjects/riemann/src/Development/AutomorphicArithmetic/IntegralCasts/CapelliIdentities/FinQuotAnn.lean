import Mathlib

theorem UpperTheory.Reformulated.B.Qi2b.fin_quot_ann :
    ∀ {Λ R M : Type} [inst : CommRing Λ] [IsNoetherianRing Λ]
    [inst_2 : CommRing R] [inst_3 : Algebra Λ R] [inst_4 : AddCommGroup M] [inst_5 : _root_.Module R M]
    [inst_6 : _root_.Module Λ M] [IsScalarTower Λ R M] [Module.Finite Λ M],
    Module.Finite Λ (R ⧸ Module.annihilator R M) := by
  intro Λ R M _ _ _ _ _ _ _ _ _
  let f : R →ₐ[Λ] Module.End Λ M := Algebra.lsmul Λ Λ M
  have hf : ∀ r : R, r ∈ Module.annihilator R M ↔ f r = 0 := by
    intro r
    rw [Module.mem_annihilator, LinearMap.ext_iff]
    rfl
  let g : (R ⧸ Module.annihilator R M) →ₐ[Λ] Module.End Λ M :=
    Ideal.Quotient.liftₐ _ f (fun r hr => (hf r).1 hr)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hf r).2 hx)
  haveI : IsNoetherian Λ (Module.End Λ M) := inferInstance
  exact Module.Finite.of_injective g.toLinearMap hg
