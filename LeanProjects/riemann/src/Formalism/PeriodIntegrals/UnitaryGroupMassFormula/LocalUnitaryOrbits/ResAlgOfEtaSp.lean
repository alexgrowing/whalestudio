import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ThetaSpanHolds

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def EtaIn : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → (IE (E := E) v).IsPrime →
    ∀ x : Fv F v ⊗[F] E, x * x = x → x = 0 ∨ x = 1

def EtaSp : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ¬ (IE (E := E) v).IsPrime →
    ∃ x : Fv F v ⊗[F] E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1

theorem etaLink_of (hI : EtaIn σ J ψ v) (hS : EtaSp σ J ψ v) : EtaLink σ J ψ v := by
  intro hstd hun
  unfold etaV
  constructor
  · intro h hp
    split_ifs at h with hx
    · obtain ⟨x, h1, h2, h3⟩ := hx
      rcases hI hstd hun hp x h1 with h0 | h0
      · exact h2 h0
      · exact h3 h0
  · intro hp
    rw [if_pos (hS hstd hun hp)]

theorem resAlg_of_etaSp (hI : EtaIn σ J ψ v) (hS : EtaSp σ J ψ v) : ResAlg σ J ψ v :=
  resAlg_of_eta σ J ψ v (etaLink_of σ J ψ v hI hS)

end PI.OmLocU.Red
