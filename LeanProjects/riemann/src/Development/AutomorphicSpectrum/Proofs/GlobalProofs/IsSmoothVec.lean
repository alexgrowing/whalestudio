import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def mnorm (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ a, ∑ b, ‖X a b‖

def wt (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := (gᴴ * g).trace.re

def IsSmoothVec (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ F : (Fin n → Fin n → ℂ) → H, ContDiff ℝ ∞ F ∧ ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z

def WordBound (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ HCSS.lieOf G) →
    ‖l.foldr (dRep π) v‖ ≤ C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod

def AlmostIsom (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ (Q : H → H → ℂ) (m M a : ℝ), 0 < m ∧ 0 ≤ M ∧ 0 ≤ a ∧
    (∀ x y z, Q x (y + z) = Q x y + Q x z) ∧ (∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) ∧
    (∀ x y, Q y x = star (Q x y)) ∧ (∀ x, m * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ (∀ x y, ‖Q x y‖ ≤ M * ‖x‖ * ‖y‖) ∧
    ∀ X ∈ HCSS.lieOf G, ∀ (t : ℝ) (x : H),
      (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re ≤
        Real.exp (a * |t| * mnorm X) * (Q x x).re

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
