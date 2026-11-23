import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.MainNotions.S

def FastCoef (k r : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) : Prop :=
  w ≠ 0 ∧ ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), gN g ^ a * ‖⟪w, σ g w⟫_ℂ‖ ≤ C

def L2BoundedOnSmooth {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Wp : Type*}
    [NormedAddCommGroup Wp] (ν : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ C : ℝ≥0, ∀ v ∈ smoothVecs (k := k) (r := r) σ,
    l2SG (k := k) (r := r) ν (fun g => B (σ g v)) ≤ (C : ℝ≥0∞) * (‖v‖₊ : ℝ≥0∞) ^ 2

def stJSZL2 : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (B₁ B₂ : L.Hs → L.Wp) (w : L.Hs) (μG μS ν : Measure (Mt k r)),
    1 ≤ k → L.c ≠ 0 → FastCoef k r L.σ w (4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → Formalism.MainNotions.S.IsHaarOn (Sset k r L.z) μS →
    IsQuotMeas (k := k) (r := r) μG μS ν →
    IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B₁ →
    IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B₂ →
    L2BoundedOnSmooth ν L.σ B₁ → L2BoundedOnSmooth ν L.σ B₂ →
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v ∈ smoothVecs (k := k) (r := r) L.σ, a • B₁ v + b • B₂ v = 0

def stJSZord : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (B₁ B₂ : L.Hs → L.Wp) (w : L.Hs) (N : ℕ) (A : ℝ),
    1 ≤ k → L.c ≠ 0 → w ∈ smoothVecs (k := k) (r := r) L.σ →
    4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ A → 2 * (N : ℝ) + ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 1 ≤ A →
    FastCoef k r L.σ w A →
    IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B₁ →
    IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B₂ →
    Formalism.MainNotions.CayleySignature.HasOrdLe k r N L.σ B₁ → Formalism.MainNotions.CayleySignature.HasOrdLe k r N L.σ B₂ →
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v ∈ smoothVecs (k := k) (r := r) L.σ, a • B₁ v + b • B₂ v = 0

def StDecSmooth : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∃ w' ∈ smoothVecs (k := k) (r := r) X.σ, ‖w'‖ = 1 ∧
      ∃ C : ℝ, ∀ x ∈ GV k r, ‖⟪w', X.σ x w'⟫_ℂ‖ ≤ C * gN x ^ (-X.a)

def StSmoothFacts : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    (0 : X.Hs) ∈ smoothVecs (k := k) (r := r) X.σ ∧
    (∀ v ∈ smoothVecs (k := k) (r := r) X.σ, ∀ v' ∈ smoothVecs (k := k) (r := r) X.σ,
      v + v' ∈ smoothVecs (k := k) (r := r) X.σ) ∧
    (∀ c : ℂ, ∀ v ∈ smoothVecs (k := k) (r := r) X.σ, c • v ∈ smoothVecs (k := k) (r := r) X.σ) ∧
    (∀ g ∈ GV k r, ∀ v ∈ smoothVecs (k := k) (r := r) X.σ, X.σ g v ∈ smoothVecs (k := k) (r := r) X.σ) ∧
    Dense (smoothVecs (k := k) (r := r) X.σ) ∧
    ∀ B : X.Hs → Wp,
      (∀ v ∈ smoothVecs (k := k) (r := r) X.σ, ∀ v' ∈ smoothVecs (k := k) (r := r) X.σ, B (v + v') = B v + B v') →
      (∀ c : ℂ, ∀ v ∈ smoothVecs (k := k) (r := r) X.σ, B (c • v) = c • B v) →
      IsCWCont (k := k) (r := r) X.σ B →
      ∀ v ∈ smoothVecs (k := k) (r := r) X.σ, ContinuousOn (fun g => B (X.σ g v)) (GV k r)

def StMOrd : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ l : X.Hs → Wp, IsMultOneMap D X l →
    X.w ∈ smoothVecs (k := k) (r := r) X.σ → ∀ N : ℕ, 2 * (N : ℝ) + AG k r + 1 ≤ X.a →
    ∀ B₁ B₂ : X.Hs → Wp,
      IsBesselMapSm (k := k) (r := r) D.z (psi k r D.z cStd) X.σ D.π B₁ →
      IsBesselMapSm (k := k) (r := r) D.z (psi k r D.z cStd) X.σ D.π B₂ →
      Formalism.MainNotions.CayleySignature.HasOrdLe k r N X.σ B₁ → Formalism.MainNotions.CayleySignature.HasOrdLe k r N X.σ B₂ →
      ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v ∈ smoothVecs (k := k) (r := r) X.σ, a • B₁ v + b • B₂ v = 0

end ReciprocityTheory.ChartRestriction.DS.Mult1
