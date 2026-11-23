import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeDeepQ
import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge

noncomputable section

namespace Formalism.L2.S.S7.DeepK

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal NNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.MainNotions.BridgeDeepQ
open Formalism.HermitianLatticeCounting.S7 (P0 b1 beP)

variable (X : CData)

abbrev dimG : ℕ := X.I.n ^ 2 * X.I.f

def hsInner (A B : Matrix (Fin X.I.n) (Fin X.I.n) ℂ) : ℝ := (Matrix.trace (A * Bᴴ)).re

def IsOneParam (v : InfinitePlace X.I.F) (E : Matrix (Fin X.I.n) (Fin X.I.n) ℂ) (c : ℝ → X.I.Ginf) : Prop :=
  Continuous c ∧ ∀ t : ℝ, (((c t v : (Matrix (Fin X.I.n) (Fin X.I.n) ℂ)ˣ)) : Matrix (Fin X.I.n) (Fin X.I.n) ℂ) = NormedSpace.exp ((t : ℂ) • E) ∧
    ∀ v', v' ≠ v → c t v' = 1

def IsLieDer (c : ℝ → X.I.Ginf) (u u' : X.Hs) : Prop := HasDerivAt (fun t : ℝ => X.σs (c t) u) u' 0

def Reach : ℕ → Set X.Hs
  | 0 => {X.tens X.w}
  | P + 1 => Reach P ∪ {u' | ∃ u ∈ Reach P, ∃ (v : InfinitePlace X.I.F) (E : Matrix (Fin X.I.n) (Fin X.I.n) ℂ) (c : ℝ → X.I.Ginf),
      Formalism.REAL.inG (X.I.ε v) E ∧ hsInner X E E ≤ 1 ∧ IsOneParam X v E c ∧ IsLieDer X c u u'}

def IsFrame (pl : Fin (dimG X) → InfinitePlace X.I.F) (E : Fin (dimG X) → Matrix (Fin X.I.n) (Fin X.I.n) ℂ) : Prop :=
  (∀ j, Formalism.REAL.inG (X.I.ε (pl j)) (E j)) ∧
    (∀ j k, pl j = pl k → hsInner X (E j) (E k) = if j = k then 1 else 0) ∧
    ∀ v A, Formalism.REAL.inG (X.I.ε v) A → A ∈ Submodule.span ℝ (E '' {j | pl j = v})

def thetaP (c : Fin (dimG X) → ℝ → X.I.Ginf) (t : Fin (dimG X) → ℝ) : ℕ → X.I.Ginf
  | 0 => 1
  | m + 1 => thetaP c t m * (if h : m < dimG X then c ⟨m, h⟩ (t ⟨m, h⟩) else 1)

def theta (c : Fin (dimG X) → ℝ → X.I.Ginf) (t : Fin (dimG X) → ℝ) : X.I.Ginf := thetaP X c t (dimG X)

def FrameExists : Prop :=
  ∃ (pl : Fin (dimG X) → InfinitePlace X.I.F) (E : Fin (dimG X) → Matrix (Fin X.I.n) (Fin X.I.n) ℂ) (c : Fin (dimG X) → ℝ → X.I.Ginf),
    IsFrame X pl E ∧ ∀ j, IsOneParam X (pl j) (E j) (c j)

def SmoothFamily (M : ℕ) (F : Fin M → X.Hs → X.I.GA → ℂ) : Prop :=
  (∀ i u, ∀ γ ∈ X.I.GFset, ∀ y, F i u (γ * y) = F i u y) ∧
    (∀ i u y, ∀ k ∈ X.I.Kg X.g, F i u (y * (1, k)) = F i u y) ∧
    (∀ P, ∀ u ∈ Reach X P, ∀ i xf, Continuous fun g : X.I.Ginf => F i u (g, xf)) ∧
    (∀ P, ∀ u ∈ Reach X P, ∀ i, Measurable (F i u)) ∧
    (∀ P, ∀ u ∈ Reach X P, ∀ (v : InfinitePlace X.I.F) (E : Matrix (Fin X.I.n) (Fin X.I.n) ℂ) (c : ℝ → X.I.Ginf),
      Formalism.REAL.inG (X.I.ε v) E → IsOneParam X v E c →
        ∃ u', IsLieDer X c u u' ∧ ∀ i y t, HasDerivAt (fun s : ℝ => F i u (y * (c s, 1))) (F i u' (y * (c t, 1))) t) ∧
    ∀ P, ∀ u ∈ Reach X P, ∫⁻ x, ∑ i, (‖F i u x‖₊ : ℝ≥0∞) ^ 2 ∂X.μ = ENNReal.ofReal ((M : ℝ) * ‖u‖ ^ 2)

def SmoothModel : Prop :=
  ∃ F : Fin (X.I.Dcount X.σs X.μf X.fund X.R X.Re) → X.Hs → X.I.GA → ℂ,
    (∀ᵐ x ∂X.μ, (X.kerD x).re = ∑ i, ‖F i (X.tens X.w) x‖ ^ 2) ∧ SmoothFamily X _ F

def CasimirStep : Prop :=
  ∀ P, ∀ u ∈ Reach X P, ∀ (v : InfinitePlace X.I.F) (E : Matrix (Fin X.I.n) (Fin X.I.n) ℂ) (c : ℝ → X.I.Ginf) (u' : X.Hs),
    Formalism.REAL.inG (X.I.ε v) E → hsInner X E E ≤ 1 → IsOneParam X v E c → IsLieDer X c u u' → ‖u'‖ ≤ beP X.I.n P X.b * ‖u‖

def Unfold (S : CSize X) : Prop :=
  X.μf.IsHaarMeasure → X.I.IsFundDom (X.I.muA X.μf) X.fund → 0 < X.I.volKg X.μf X.g →
  ∀ (pl : Fin (dimG X) → InfinitePlace X.I.F) (E : Fin (dimG X) → Matrix (Fin X.I.n) (Fin X.I.n) ℂ) (c : Fin (dimG X) → ℝ → X.I.Ginf),
    IsFrame X pl E → (∀ j, IsOneParam X (pl j) (E j) (c j)) →
    ∀ s : ℝ, 0 < s → s * (X.I.n : ℝ) ^ 19 ≤ 1 → 8 * (X.I.n : ℝ) ^ 2 * s ≤ 1 →
    ∀ (y : X.I.GA) (Φ : X.I.GA → ℝ≥0∞), Measurable Φ → (∀ γ ∈ X.I.GFset, ∀ z, Φ (γ * z) = Φ z) →
      (∀ z, ∀ k ∈ X.I.Kg X.g, Φ (z * (1, k)) = Φ z) →
      ∫⁻ t in Set.Icc (0 : Fin (dimG X) → ℝ) (fun _ => s), Φ (y * (theta X c t, 1)) ≤
        ENNReal.ofReal (Real.exp (X.I.f : ℝ) * (1 + 4 * Real.sqrt (X.I.n : ℝ) / S.tau1 y ^ 2) ^ (2 * dimG X) /
          X.I.volKg X.μf X.g) * ∫⁻ z, Φ z ∂X.μ

def KerDeepA (S : CSize X) (volK : ℝ) : Prop :=
  ∀ᵐ x ∂X.μ, S.tau1 x < 1 / 2 → |(X.kerD x).re| ≤ sobT X (S.tau1 x) volK

def sobTM (t volK : ℝ) (M : ℕ) : ℝ :=
  (6 * beP X.I.n (P0 X.I.n X.qq X.I.f + X.I.n ^ 2 * X.I.f) X.b) ^ (X.I.n ^ 2 * X.I.f) * Real.exp (X.I.f : ℝ) *
    (17 * Real.sqrt (X.I.n : ℝ) / t ^ 2) ^ (2 * X.I.n ^ 2 * X.I.f) * (M : ℝ) / volK

def KerDeepAFam (S : CSize X) (volK : ℝ) (M : ℕ) (F : Fin M → X.Hs → X.I.GA → ℂ) : Prop :=
  ∀ x, S.tau1 x < 1 / 2 → ∑ i, ‖F i (X.tens X.w) x‖ ^ 2 ≤ sobTM X (S.tau1 x) volK M

def TFMaps (T : Fin (X.I.Dcount X.σs X.μf X.fund X.R X.Re) → (X.Hs →L[ℂ] X.L2)) : Prop :=
  (∀ i, T i ∈ X.I.HomS X.σs X.μf X.fund X.R) ∧ (∀ i u, X.Re (T i u) = T i u) ∧ (∀ i u u', ⟪T i u, T i u'⟫_ℂ = ⟪u, u'⟫_ℂ) ∧
    (∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0) ∧ (∀ i u, ∀ k ∈ X.I.Kg X.g, X.R (1, k) (T i u) = T i u) ∧
    (∀ i u, X.I.IsCuspFn X.μ (X.I.ext (T i u))) ∧
    ∀ Top : X.L2 →L[ℂ] X.L2, X.IsOp Top → IsStarProjection Top →
      ∃ B : OrthonormalBasis (Fin (X.I.Dcount X.σs X.μf X.fund X.R X.Re)) ℂ (X.rg Top), ∀ i, ((B i : X.rg Top) : X.L2) = T i (X.tens X.w)

def SmoothReps (T : Fin (X.I.Dcount X.σs X.μf X.fund X.R X.Re) → (X.Hs →L[ℂ] X.L2))
    (F : Fin (X.I.Dcount X.σs X.μf X.fund X.R X.Re) → X.Hs → X.I.GA → ℂ) : Prop :=
  (∀ P, ∀ u ∈ Reach X P, ∀ i, F i u =ᵐ[X.μ] (T i u : X.I.GA → ℂ)) ∧
    (∀ i u, ∀ γ ∈ X.I.GFset, ∀ y, F i u (γ * y) = F i u y) ∧
    (∀ i u y, ∀ k ∈ X.I.Kg X.g, F i u (y * (1, k)) = F i u y) ∧
    (∀ P, ∀ u ∈ Reach X P, ∀ i xf, Continuous fun g : X.I.Ginf => F i u (g, xf)) ∧
    (∀ P, ∀ u ∈ Reach X P, ∀ i, Measurable (F i u)) ∧
    ∀ P, ∀ u ∈ Reach X P, ∀ (v : InfinitePlace X.I.F) (E : Matrix (Fin X.I.n) (Fin X.I.n) ℂ) (c : ℝ → X.I.Ginf),
      Formalism.REAL.inG (X.I.ε v) E → IsOneParam X v E c →
        ∃ u', IsLieDer X c u u' ∧ ∀ i y t, HasDerivAt (fun s : ℝ => F i u (y * (c s, 1))) (F i u' (y * (c t, 1))) t

end Formalism.L2.S.S7.DeepK

end
