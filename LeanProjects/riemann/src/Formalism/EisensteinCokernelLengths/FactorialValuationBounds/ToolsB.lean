import Formalism.EisensteinCokernelLengths.CokernelLengthBoundOfLifts
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound

namespace Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.FactorialValuationBoundsFacts
open Formalism.WachCohomologyFacts

theorem key {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (Z Z₀ I : Submodule O M)
    (hZ₀Z : Z₀ ≤ Z) :
    Module.length O (↥Z ⧸ I.comap Z.subtype) =
      Module.length O (↥Z₀ ⧸ I.comap Z₀.subtype) + Module.length O (↥Z ⧸ (Z₀ ⊔ I).comap Z.subtype) := by
  set I' := I.comap Z.subtype
  set J' := (Z₀ ⊔ I).comap Z.subtype
  set I₀ := I.comap Z₀.subtype
  have hIJ : I' ≤ J' := Submodule.comap_mono le_sup_right
  let f : ↥Z₀ →ₗ[O] ↥Z ⧸ I' := I'.mkQ ∘ₗ Submodule.inclusion hZ₀Z
  have hker : LinearMap.ker f = I₀ := by
    ext x
    simp only [f, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, I', I₀, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_inclusion]
  let f' := I₀.liftQ f hker.ge
  let g := I'.mapQ J' LinearMap.id hIJ
  have hf' : Function.Injective f' := by
    rw [← LinearMap.ker_eq_bot]; exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have hg : Function.Surjective g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H z => exact ⟨Submodule.Quotient.mk z, rfl⟩
  have hex : Function.Exact f' g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, J',
        Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_sup]
      constructor
      · rintro ⟨a, ha, b, hb, hab⟩
        refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
        simp only [f', Submodule.liftQ_apply, f, LinearMap.coe_comp, Function.comp_apply,
          Submodule.mkQ_apply]
        rw [Submodule.Quotient.eq]
        simp only [I', Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
          Submodule.coe_inclusion]
        have : (a : M) - z = -b := by rw [← hab]; abel
        rw [this]; exact I.neg_mem hb
      · rintro ⟨w, hw⟩
        induction w using Submodule.Quotient.induction_on with
        | H a =>
          simp only [f', Submodule.liftQ_apply, f, LinearMap.coe_comp, Function.comp_apply,
            Submodule.mkQ_apply] at hw
          rw [Submodule.Quotient.eq] at hw
          simp only [I', Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
            Submodule.coe_inclusion] at hw
          refine ⟨a, a.2, (z : M) - a, ?_, by abel⟩
          have := I.neg_mem hw; simpa using this
  exact Module.length_eq_add_of_exact f' g hf' hg hex

theorem lenBound2 : Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.LenBound2 := by
  intro O M _ _ _ ℓ g g₀ e e' Z Bc I s s₀ hs hZ hBc hs₀ hs₀Z hke hke'
  have hZ₀Z : Submodule.span O (s₀ : Set M) ≤ Z := Submodule.span_le.mpr hs₀Z
  have h1 := quotientLengthBound_holds O M ℓ g e Z Bc (Submodule.span O (s₀ : Set M) ⊔ I) s hs hZ
    (hBc.trans le_sup_right) hke
  have h2 := quotientLengthBound_holds O M ℓ g₀ e' (Submodule.span O (s₀ : Set M)) ⊥ I s₀ hs₀ (by simp)
    bot_le hke'
  rw [key Z _ I hZ₀Z]
  calc _ ≤ (g₀ : ℕ∞) * (e' : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) +
        (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := add_le_add h2 h1
    _ = _ := by ring

end Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.FactorialValuationBoundsFacts
