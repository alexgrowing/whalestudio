import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtDelta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def dbarPair {D : ℕ} (f : (Fin D → ℂ) → ℂ) (y ξ : Fin D → ℂ) : ℂ :=
  ∑ l, dbarC f y l * conj (ξ l)

def extPsi {D : ℕ} {X : EmbDatum D} (Z : ZeroDatum X) (j : ℕ) (δ : ℝ) (k : Fin X.A.n) (y : X.U) :
    ℝ :=
  X.wt (D + j) k y + D * Real.log (extEv Z k y + δ ^ 2)

def extPhi {D : ℕ} {X : EmbDatum D} (Z : ZeroDatum X) (ε : ℝ) (k : Fin X.A.n) (y : X.U) : ℝ :=
  curvPhi (extX ε (extEv Z k y))

def extTheta (ε t : ℝ) : ℝ :=
  curvK (extX ε t) * ε ^ 2 / (curvEta (extX ε t) * t) +
    1 / (extX ε t ^ 2 * curvEta (extX ε t)) + (curvK (extX ε t) / curvEta (extX ε t)) ^ 2

def extOmega {D : ℕ} {X : EmbDatum D} (Z : ZeroDatum X) (ε : ℝ) (k : Fin X.A.n)
    (y ξ : Fin D → ℂ) : ℝ :=
  ‖dbarPair (fun z => (extEv Z k ((X.A.chart k).symm z) : ℂ)) y ξ‖ ^ 2 /
    (extEv Z k ((X.A.chart k).symm y) + ε ^ 2) ^ 2

def extShell (ε t : ℝ) : ℝ :=
  (Set.Icc (ε ^ 2 / 2) (ε ^ 2)).indicator 1 t

def chartInner {D : ℕ} {U : Type} [TopologicalSpace U] (A : FinHolAtlas D U)
    (ψ : Fin A.n → U → ℝ) (F G : Fin A.n → U → ℂ) : ℂ :=
  ∑ k, ∫ y in piece A k, F k ((A.chart k).symm y) * conj (G k ((A.chart k).symm y)) *
    ((2 ^ D * Real.exp (-ψ k ((A.chart k).symm y)) : ℝ) : ℂ)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
