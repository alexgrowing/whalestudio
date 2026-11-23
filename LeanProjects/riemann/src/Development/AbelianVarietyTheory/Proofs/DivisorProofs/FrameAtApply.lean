import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply

set_option autoImplicit false

noncomputable section

open Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

namespace GlobalTheory.TorsionForm.Gauge

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

def frameAt (n : ℕ) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (b : E) :
    Ext (n + n + g) →L[ℂ] Ext (n + n + g) :=
  frameMap n (den γ (τ b))

def gauge (n : ℕ) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (s : Pt E g → Ext (n + n + g))
    (Q : Pt E g) : Ext (n + n + g) :=
  frameAt n τ γ Q.1 (s (reframe τ γ Q))

theorem frameAt_apply (n : ℕ) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (b : E)
    (w : Ext (n + n + g)) : frameAt n τ γ b w = frameMap n (den γ (τ b)) w := rfl

end GlobalTheory.TorsionForm.Gauge
