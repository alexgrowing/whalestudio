import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoreStep

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.SRW

def FrameP {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {r : ℕ} {T : E}
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V) (f : Fin r → S.V) : Prop :=
  (∀ a b, S.hT (F0.e a) (f b) = if a = b then 1 else 0) ∧ (∀ b, S.hT (f b) F0.z = 0) ∧
    (∀ b, ∀ x ∈ Λ, S.hT (f b) x ∈ aa b)

def FrameStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V), CoreHyp S aa F0 Λ → ∃ f, FrameP S aa F0 Λ f

def DualEStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V), CoreHyp S aa F0 Λ → ∀ b, ∀ x ∈ Λ, S.hT (F0.e b) x ∈ (aa b)⁻¹

def DualFStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V), CoreHyp S aa F0 Λ → ∀ f, FrameP S aa F0 Λ f →
      ∀ b, ∀ y ∈ (aa b)⁻¹, y • f b ∈ Λ

def IsoStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V), CoreHyp S aa F0 Λ → ∀ f, FrameP S aa F0 Λ f →
      ∃ f', FrameP S aa F0 Λ f' ∧ ∀ a b, S.hT (f' a) (f' b) = 0

def AsmStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V), CoreHyp S aa F0 Λ → ∀ f, FrameP S aa F0 Λ f →
      (∀ a b, S.hT (f a) (f b) = 0) → Formalism.L2.SG.Saturated.IsSplitBy aa F0 Λ

theorem coreStep_of (h1 : FrameStep) (h2 : IsoStep) (h3 : AsmStep) : CoreStep := by
  intro E _ _ _ S r T aa F0 Λ hC
  obtain ⟨f, hf⟩ := h1 E S r T aa F0 Λ hC
  obtain ⟨f', hf', hiso⟩ := h2 E S r T aa F0 Λ hC f hf
  exact h3 E S r T aa F0 Λ hC f' hf' hiso

end PI.SRW
