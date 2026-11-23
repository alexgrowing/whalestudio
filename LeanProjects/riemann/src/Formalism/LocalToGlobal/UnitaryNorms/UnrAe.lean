import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

def UnrAE (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ χ : Ideles L →* ℂˣ, Continuous χ →
    ∀ᶠ v in Filter.cofinite, ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → χ (localIdele L v x) = 1

def SMOne (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ χ χ' : HChar L, (∀ᶠ v in Filter.cofinite, χ.UnrAt v ∧ χ'.UnrAt v ∧ χ.val v = χ'.val v) → χ = χ'

variable {L : Type} [Field L] [NumberField L]

theorem HChar.unr_ae (h : UnrAE L) (χ : HChar L) : ∀ᶠ v in Filter.cofinite, χ.UnrAt v := by
  have hc : Continuous (χ.1 : Ideles L →* ℂˣ) := χ.2.1
  exact (h χ.1 hc).mono fun v hv x hx => hv x hx

end Formalism.L2.Host
