import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.BesselIsometryScalar
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def KV {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) :
    Submodule ℂ H :=
  Submodule.span ℂ {x | ∃ g ∈ UH (Hpk k r), ∃ v, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ v ∧ x = σ g v}

def muHN {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) :=
  (μW.prod μN).map (fun p : Mt k r × Mt k r => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)

def BesselMapEquivariance {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r))
    (σ : Mat k r → (H →L[ℂ] H)) : Prop :=
  ∃ l : H → Wp,
    (∀ u ∈ KV σ, ∀ v ∈ KV σ, l (u + v) = l u + l v) ∧ (∀ (a : ℂ), ∀ u ∈ KV σ, l (a • u) = a • l u) ∧
    (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, ∀ v ∈ KV σ, l (σ (h * m) v) = psi k r z c m • π h (l v)) ∧
    (∀ u ∈ KV σ, ∀ v ∈ KV σ,
      Integrable (fun p : Mt k r × Mt k r =>
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹)
        (μW.prod μN) ∧
      ∫ p : Mt k r × Mt k r,
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹
        ∂(μW.prod μN) = (innerSL ℂ (l v)).smulRight (l u)) ∧
    ∀ u ∈ KV σ, u ≠ 0 → ∀ v ∈ KV σ,
      ENNReal.ofReal (‖l v‖ ^ 2) * Formalism.MainNotions.S.l2SG (k := k) (r := r) ν (fun g => l (σ g u)) =
        ENNReal.ofReal (‖u‖ ^ 2 * ‖l v‖ ^ 2 / Formalism.MainNotions.S.fdegH μG σ u)

def StNormL : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X → aM k r ≤ X.a →
    ∀ l : X.Hs → Wp, IsMultOneMap D X l → ∀ d : ℝ, IsFdegG D X d → ∀ ν : Measure (Mt k r),
      Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν → ∀ u ∈ Vfl X, ∀ v ∈ Vfl X,
        ENNReal.ofReal (‖l v‖ ^ 2) * Formalism.MainNotions.S.l2SG (k := k) (r := r) ν (fun g => l (X.σ g u)) =
          ENNReal.ofReal (‖u‖ ^ 2 * ‖l v‖ ^ 2 / d)

def LocalDataToSetting : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r)),
    1 ≤ k → c ≠ 0 → inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsURepOn (UWset k r z) π → Formalism.MainNotions.S.IsIrredOn (UWset k r z) π →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Nset k r) μN → Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG →
    Formalism.MainNotions.S.IsQuotMeas μG (muHN μW μN) ν →
    ∃ (D : RealPlaceData k r Wp Wp) (t : Mat k r), IsDiag D ∧ D.z = z ∧ D.π = π ∧ D.μG = μG ∧ t ∈ GV k r ∧
      (∀ h ∈ UWset k r z, t * h = h * t) ∧
      (∀ m ∈ Nset k r, t * m * t⁻¹ ∈ Nset k r ∧ t⁻¹ * m * t ∈ Nset k r ∧ psi k r z c (t * m * t⁻¹) = psiD D m) ∧
      MeasurePreserving (fun p : Mt k r × Mt k r =>
        ((p.1, fun i j => (t⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹) * t) i j) : Mt k r × Mt k r))
        (μW.prod μN) (D.μW.prod D.μN) ∧
      Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) (ν.map fun x : Mt k r => fun i j => (t⁻¹ * Matrix.of x * t) i j)

def LocalSquareIntegrableKFinite : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mat k r → (Wp →L[ℂ] Wp)) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (μW μN μG ν : Measure (Mt k r)) (a : ℝ),
    1 ≤ k → c ≠ 0 → inWb k r z → 0 < Tz k r z → 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ a →
    Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ → Formalism.MainNotions.S.IsIrredOn (UH (Hpk k r)) σ →
    Formalism.MainNotions.S.IsURepOn (UWset k r z) π → Formalism.MainNotions.S.IsIrredOn (UWset k r z) π →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Nset k r) μN → Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG →
    Formalism.MainNotions.S.IsQuotMeas μG (muHN μW μN) ν →
    (∀ v w : H, MemLp (fun x : Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ) 2 μG) →
    (∀ v v' : H, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ v → Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ v' →
      ∃ C : ℝ, ∀ x ∈ UH (Hpk k r), ‖⟪v', σ x v⟫_ℂ‖ ≤ C * gN x ^ (-a)) →
    (∃ w₀ : H, w₀ ≠ 0 ∧ Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ w₀) →
    BesselMapEquivariance z c π μW μN μG ν σ

def AdmissibleAtRealPlace (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (u : D.what₂.Word) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat D.R.k D.R.rS → (H →L[ℂ] H))
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mat D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (w : H)
    (μW μN μG ν : Measure (Mt D.R.k D.R.rS)),
    Formalism.MainNotions.S.IsRowsDS D τ σ → Formalism.MainNotions.S.IsColsType D u τ z π →
    (∀ a : Fin D.R.rS, z (eI D.R.k D.R.rS a) = 0 ∧ z (esI D.R.k D.R.rS a) = 0) →
    0 < Tz D.R.k D.R.rS z →
    Formalism.MainNotions.S.IsLowUnitH D.R.k D.R.rS (Formalism.MainNotions.S.epsSH D.R) (Formalism.MainNotions.S.lamSH D.R (D.hc τ)) σ w →
    Formalism.MainNotions.S.IsHaarOn (UWset D.R.k D.R.rS z) μW → Formalism.MainNotions.S.IsHaarOn (Nset D.R.k D.R.rS) μN →
    Formalism.MainNotions.S.IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → Formalism.MainNotions.S.IsQuotMeas μG (muHN μW μN) ν →
    BesselMapEquivariance z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) π μW μN μG ν σ

def LocalMultiplicityOne : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (Ca : ℝ), Formalism.MainNotions.LocalBesselAndTopKernel.FormalDegreeDecay D Ca → 1 ≤ Ca → 1 ≤ D.R.k → D.R.r = 2 * D.R.rS + D.R.k + 1 →
    (2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) ≠ 0 → AdmissibleAtRealPlace D

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down
