import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.ZModInj

namespace KStar.Selmer

open Matrix Module

variable {N : ℕ} [NeZero N] {M M' : Type*} [AddCommGroup M] [Module (ZMod N) M] [AddCommGroup M']
  [Module (ZMod N) M']

private theorem finite_dual [Finite M] : Finite (Module.Dual (ZMod N) M) :=
  Finite.of_injective (fun f : Module.Dual (ZMod N) M => (f : M → ZMod N)) DFunLike.coe_injective

private theorem card_dual_le [Finite M] : Nat.card (Module.Dual (ZMod N) M) ≤ Nat.card M := by
  haveI := finite_dual (N := N) (M := M)
  haveI := Fintype.ofFinite M
  let Φ : Module.Dual (ZMod N) M → AddChar M ℂ := fun f =>
    ZMod.stdAddChar.compAddMonoidHom f.toAddMonoidHom
  have hΦ : Function.Injective Φ := by
    intro f g h
    ext m
    have := DFunLike.congr_fun h m
    simp only [Φ, AddChar.compAddMonoidHom_apply] at this
    exact ZMod.injective_stdAddChar this
  calc Nat.card (Module.Dual (ZMod N) M) ≤ Nat.card (AddChar M ℂ) :=
        Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card M := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

private theorem eval_inj : Function.Injective (Module.Dual.eval (ZMod N) M) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro m hm
  by_contra hne
  obtain ⟨f, -, hf⟩ := exists_form_ne_zero (⊥ : Submodule (ZMod N) M) (z := m)
    (by simpa using hne)
  exact hf (by simpa using DFunLike.congr_fun (LinearMap.mem_ker.1 hm) f)

theorem card_dual [Finite M] : Nat.card (Module.Dual (ZMod N) M) = Nat.card M := by
  refine le_antisymm card_dual_le ?_
  have h1 : Finite (Module.Dual (ZMod N) M) := finite_dual
  have h2 : Finite (Module.Dual (ZMod N) (Module.Dual (ZMod N) M)) := finite_dual
  exact (Nat.card_le_card_of_injective _ (eval_inj (N := N) (M := M))).trans card_dual_le

end KStar.Selmer
