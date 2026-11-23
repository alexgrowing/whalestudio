import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.EtaCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt

namespace GlobalTheory.CompanionTheory.Ar.ThA

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def wabs (X : Data E r) (la : Wt X.Ψ r) : ℝ := ∑ τ, ∑ i, |(la τ i : ℝ)|

def GapsGe (X : Data E r) (la : Wt X.Ψ r) (g : ℝ) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → (la τ j : ℝ) + g ≤ la τ i) ∧
    ∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → 0 < X.p0 → X.p0 < r → (la τ i0 : ℝ) + g ≤ la τ i1

def rhoW (X : Data E r) : Wt X.Ψ r := fun _ a =>
  if (a : ℕ) < X.p0 then -(((r : ℤ) - X.p0) + (a : ℕ)) else -(((a : ℕ) : ℤ) - X.p0)

def delW (X : Data E r) : Wt X.Ψ r := fun _ a => if (a : ℕ) < X.p0 then -1 else 0

def rad0 (r : ℕ) : ℝ := 1 / (1116 * (r : ℝ))

def nrm2 (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) : ℝ :=
  (∫ z in FF, X.pnorm la P (cpt X x0 z) ^ 2 ∂muF X x0) / (muF X x0 FF).toReal

def BergLB (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (la : Wt X.Ψ r)
    (x : Frame X.Ψ r) (t : ℝ) : Prop :=
  ∃ P ∈ X.SS la, 0 < nrm2 X x0 FF la P ∧ t * nrm2 X x0 FF la P ≤ X.pnorm la P x ^ 2

def FinDimSS (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS la, ∃ c : Fin K → ℂ,
    ∀ x ∈ X.dom, f x = ∑ i, c i * g i x

def HasLevel (X : Data E r) (c : ℕ) : Prop :=
  ∀ γ ∈ X.Γ, ∀ v ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (c : E) • y

def InjBall (X : Data E r) (x1 : Frame X.Ψ r) (ρ : ℝ) : Prop :=
  Metric.ball 0 ρ ⊆ OmF X x1 ∧
  ∀ γ ∈ X.Γ, ∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∀ z' ∈ Metric.ball (0 : V (nd X)) ρ,
    ∀ b ∈ Bor X.Ψ r, cpt X x1 z' = lact γ (rmul (cpt X x1 z) b) → γ = 1

def satG (X : Data E r) (x1 : Frame X.Ψ r) (S : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z ∈ S, x = lact γ (rmul (cpt X x1 z) b)}

def IsSmSec (X : Data E r) (la : Wt X.Ψ r) (F : Frame X.Ψ r → ℂ) : Prop :=
  ContDiffOn ℝ ∞ F X.dom ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, F (rmul x b) = bchar la b * F x) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, F (lact γ x) = X.χ la γ * F x

def crossDet (X : Data E r) (x y : Frame X.Ψ r) (τ : X.Ψ) : ℂ :=
  (Matrix.of fun a b : Fin X.p0 => hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a))
    (col (mat y τ) (Fin.castLE X.p0_le b))).det

def kerK (X : Data E r) (b : ℝ) (x y : Frame X.Ψ r) : ℝ :=
  ∏ τ, (‖crossDet X x x τ‖ * ‖crossDet X y y τ‖ / ‖crossDet X x y τ‖ ^ 2) ^ b

def dbarM (X : Data E r) (F : Frame X.Ψ r → ℂ) (x1 : Frame X.Ψ r) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℂ :=
  ∑ j, wdb (nd X) j (fun w => F (cpt X x1 w)) z * conj (ξ j)

def thetaM (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x1 : Frame X.Ψ r) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  leviM X (phla X (la - kapW X)) x1 z ξ - 2 * (r : ℝ) * leviM X (phla X (delW X)) x1 z ξ +
    leviM X ψ x1 z ξ

def QHyp (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (F0 : Frame X.Ψ r → ℂ)
    (a : Frame X.Ψ r → ℝ) : Prop :=
  IsInvFn X ψ ∧ ContDiffOn ℝ ∞ ψ X.dom ∧ (∃ C : ℝ, ∀ x ∈ X.dom, |ψ x| ≤ C) ∧
  IsSmSec X la F0 ∧ (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la F0 x ≤ C) ∧
  Measurable a ∧ IsInvFn X a ∧ (∃ C : ℝ, ∀ x ∈ X.dom, 0 ≤ a x ∧ a x ≤ C) ∧
  ∀ x1, IsOrth X x1 → ∀ z ∈ OmF X x1, ∀ ξ : Fin (nd X) → ℂ,
    16 * (r : ℝ) ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) * leviM X (phla X (delW X)) x1 z ξ ≤
      thetaM X la ψ x1 z ξ ∧
    ‖dbarM X F0 x1 z ξ‖ ^ 2 * X.nfac la (cpt X x1 z) ^ 2 ≤ a (cpt X x1 z) * thetaM X la ψ x1 z ξ

def CutData (X : Data E r) (la : Wt X.Ψ r) (x1 : Frame X.Ψ r) (χ : ℝ → ℝ) (δ : ℝ)
    (ψ : Frame X.Ψ r → ℝ) (F0 : Frame X.Ψ r → ℂ) (a : Frame X.Ψ r → ℝ) : Prop :=
  (∀ z ∈ Metric.ball (0 : V (nd X)) (rad0 r),
    ψ (cpt X x1 z) = (nd X : ℝ) * etaCut χ (rad0 r) δ z ∧
    F0 (cpt X x1 z) = (χ (‖z‖ ^ 2 / rad0 r ^ 2) : ℂ) ∧
    a (cpt X x1 z) ≤ if rad0 r ^ 2 / 4 ≤ ‖z‖ ^ 2 then 9 / (113 * (nd X : ℝ)) * X.nfac la (cpt X x1 z) ^ 2 else 0) ∧
  ∀ x ∈ X.dom, x ∉ satG X x1 (Metric.ball 0 (rad0 r)) → ψ x = 0 ∧ F0 x = 0 ∧ a x = 0

def HasPeriod (X : Data E r) (P : Frame X.Ψ r → ℂ) (M : ℝ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ a : E, cc a = a → IsIntegral ℤ a → ∀ x ∈ X.dom,
    P (X.flow ξ (fun τ => (M : ℂ) * τ.1 a) x) = P x

def FJSupp (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (σ : ℝ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 →
    (∀ τ, 0 ≤ ν τ) ∧ σ ≤ (∑ τ, Real.sqrt (ν τ)) ^ 2

def pp3c (E : Type) [Field E] [NumberField E] (M w : ℝ) : ℝ :=
  2 * (w + fdeg E * Real.log (4 * M * Real.sqrt (dE E)) + fdeg E * Real.log (fdeg E) + 3)

end

end GlobalTheory.CompanionTheory.Ar.ThA
