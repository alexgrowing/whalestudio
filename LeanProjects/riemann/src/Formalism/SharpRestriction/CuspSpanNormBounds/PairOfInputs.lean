import Formalism.SharpRestriction.CuspSpanNormBounds.DoubleBoundAndExtensionOfSmooth

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.DoubleDerivativeSmoothness

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def KApproxAt (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  ∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ Ws : List (List (Mx k r)), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) →
    ∀ ε : ℝ, 0 < ε → ∃ v' : H, IsKFinHpk (k := k) (r := r) σ v' ∧ v' ∈ smoothVecs (k := k) (r := r) σ ∧
      v' - v ∈ smoothVecs (k := k) (r := r) σ ∧ ‖v' - v‖ < ε ∧ ∀ w ∈ Ws, ‖dsigW σ w (v' - v)‖ < ε

def DecDDAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  ∀ u ∈ DDsp σ w0, ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ x ∈ smoothVecs (k := k) (r := r) σ, Integrable (FI z c π σ u x) (μW.prod μN) ∧
      ∫ p, ‖FI z c π σ u x p‖ ∂(μW.prod μN) ≤ C * (Ws.map fun w => ‖dsigW σ w x‖).sum

def ExtDDOf : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H),
    DDSmoothAt σ w0 → KApproxAt σ → DecDDAt z c π μW μN σ w0 → ExtDDAt z c π μW μN σ w0

def KZeroOf : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H)),
    KApproxAt σ → KZeroAt z c π σ

def DDInputs (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG νq νq' : Measure (Mt D.R.k D.R.rS)) (w0 : H),
    NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ → IsLowUnitH D.R.k D.R.rS L.ε μ σ w0 →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
      DDSmoothAt σ w0 ∧ KApproxAt σ ∧ DecDDAt L.z L.c L.π L.μW L.μN σ w0 ∧ DecDDAt L.z' L.c L.π' L.μW' L.μN σ w0

end Formalism.MainNotions.DoubleDerivativeSmoothness
