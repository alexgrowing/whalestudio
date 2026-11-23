import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

namespace GlobalTheory.VacLine

theorem slice_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (Ψ : (κ → AF F) → ℂ), Ψ ∈ schA F κ →
    (∀ y : κ → Af F, ∃ f : SInf F κ, ∀ x, slice Ψ x y = f x) ∧ ∀ x, slice Ψ x ∈ SB (κ → Af F) := by
  intro F _ _ κ _ Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    have key : ∀ x y, slice (pureA F f g) x y = f x * g y := by
      intro x y
      simp only [slice, pureA, mkPt, RingEquiv.apply_symm_apply]
    refine ⟨fun y => ⟨g y • f, fun x => ?_⟩, fun x => ?_⟩
    · rw [key, SchwartzMap.smul_apply, smul_eq_mul, mul_comm]
    · have : slice (pureA F f g) x = f x • g := by
        funext y; rw [key]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ hg
  | zero =>
    refine ⟨fun y => ⟨0, fun x => rfl⟩, fun x => ?_⟩
    exact Submodule.zero_mem _
  | add Φ Φ' _ _ h h' =>
    refine ⟨fun y => ?_, fun x => ?_⟩
    · obtain ⟨f, hf⟩ := h.1 y
      obtain ⟨f', hf'⟩ := h'.1 y
      exact ⟨f + f', fun x => by
        show slice Φ x y + slice Φ' x y = (f + f') x
        rw [hf, hf', SchwartzMap.add_apply]⟩
    · have : slice (Φ + Φ') x = slice Φ x + slice Φ' x := rfl
      rw [this]
      exact Submodule.add_mem _ (h.2 x) (h'.2 x)
  | smul a Φ _ h =>
    refine ⟨fun y => ?_, fun x => ?_⟩
    · obtain ⟨f, hf⟩ := h.1 y
      exact ⟨a • f, fun x => by
        show a • slice Φ x y = (a • f) x
        rw [hf, SchwartzMap.smul_apply]⟩
    · have : slice (a • Φ) x = a • slice Φ x := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (h.2 x)

end GlobalTheory.VacLine
