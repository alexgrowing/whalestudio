import Formalism.TruncatedSeriesCounting.LengthQuotientLeOfPowSMul
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubGen

noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

theorem length_quotient_le_of_pow_smul : LengthQuotientLeOfPowSMul := by
  intro O _ _ _ M _ _ _ _ ℓ e e' FFs J h1 h2
  set A := FFs ⊔ Ideal.span {ℓ ^ e'} • (⊤ : Submodule O M) with hA
  have hx : ∀ x ∈ A, ℓ ^ e • x ∈ J := by
    intro x hxA
    obtain ⟨f, hf, m, hm, rfl⟩ := Submodule.mem_sup.1 hxA
    rw [smul_add]
    exact J.add_mem (h1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hf))
      (J.smul_mem _ (h2 hm))
  have hS := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.submodule_generator_count O M ℓ e A J hx
  let f : (A ⧸ J.comap A.subtype) →ₗ[O] M ⧸ J := (J.comap A.subtype).mapQ J A.subtype le_rfl
  let g : (M ⧸ J) →ₗ[O] M ⧸ (A ⊔ J) :=
    J.mapQ (A ⊔ J) LinearMap.id (fun x hx => Submodule.mem_sup_right hx)
  have hf : Function.Injective f := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy ⊢
    simpa using hxy
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  have hex : Function.Exact f g := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hm
      obtain ⟨a, ha, j, hj, rfl⟩ := Submodule.mem_sup.1 hm
      refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
      simp only [f, Submodule.mapQ_apply, Submodule.coe_subtype]
      rw [Submodule.Quotient.eq]
      simpa using J.neg_mem hj
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      simp only [f, Submodule.mapQ_apply, Submodule.coe_subtype, Submodule.Quotient.eq] at hx
      have e1 : m = (a : M) - ((a : M) - m) := by abel
      rw [e1]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left a.2) (Submodule.mem_sup_right hx)
  have hlen := Module.length_eq_add_of_exact f g hf hg hex
  have hq : Module.length O (M ⧸ (A ⊔ J)) ≤ Module.length O (M ⧸ A) := by
    refine Module.length_le_of_surjective (A.mapQ (A ⊔ J) LinearMap.id (fun x hx => Submodule.mem_sup_left hx)) ?_
    intro z
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  rw [hlen, add_comm]
  exact add_le_add hq hS

end Formalism.TruncatedSeriesCounting.R9
