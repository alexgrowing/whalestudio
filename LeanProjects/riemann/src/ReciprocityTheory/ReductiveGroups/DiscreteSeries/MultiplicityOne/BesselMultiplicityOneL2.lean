import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.MainNotions.S

def IsL2BoundedBessel {k r : ℕ} (L : LocBessel k r) (B : L.Hs → L.Wp) : Prop :=
  ∃ (μG ν : Measure (Mt k r)) (C : ℝ), Formalism.FourierDecayAlt.B.IsHaarOn (GV k r) μG ∧
    IsQuotMeas μG ((L.μW.prod L.μN).map fun p => fun i j => (Matrix.of p.2 * Matrix.of p.1) i j) ν ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) L.σ,
      ∫⁻ x : Mt k r, ‖B (L.σ (Matrix.of x) v)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (C * ‖v‖ ^ 2)

def HasDecay {k r : ℕ} (L : LocBessel k r) (a : ℝ) : Prop :=
  ∃ w ∈ smoothVecs (k := k) (r := r) L.σ, ‖w‖ = 1 ∧
    ∃ C : ℝ, ∀ x ∈ GV k r, ‖⟪w, L.σ x w⟫_ℂ‖ ≤ C * gN x ^ (-a)

def BesselMultiplicityOneL2 : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (B₁ B₂ : L.Hs → L.Wp), L.c ≠ 0 → 1 ≤ k → HasDecay L (aM k r) →
    IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B₁ →
    IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B₂ →
    IsL2BoundedBessel L B₁ → IsL2BoundedBessel L B₂ →
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v ∈ smoothVecs (k := k) (r := r) L.σ, a • B₁ v + b • B₂ v = 0

end ReciprocityTheory.ChartRestriction.DS.Mult1
