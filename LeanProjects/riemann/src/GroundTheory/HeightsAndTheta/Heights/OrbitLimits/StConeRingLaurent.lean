import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChartConeObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

def ConeRingLaurent.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) (i : (k : K) → ι k),
    (ratioMap i).Flat ∧ ∀ 𝔮 : Ideal (DehomRing i), 𝔮.IsPrime → (𝔮.map (ratioMap i)).IsPrime

def evalOnesDehom {K : Type} [Fintype K] {ι : K → Type} (i : (k : K) → ι k) : DehomRing i →+* ℂ :=
  Ideal.Quotient.lift (dehomIdeal i) (eval fun _ => (1 : ℂ)) (by
    have hle : dehomIdeal i ≤ RingHom.ker (eval fun _ => (1 : ℂ) : MvPolynomial (Σ k, ι k) ℂ →+* ℂ) := by
      rw [dehomIdeal, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      simp
    exact fun a ha => hle ha)

end GroundTheory.Heights₂.Heights.Targets
