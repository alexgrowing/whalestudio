import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.L2BoundedOnSmooth
import Mathlib.Analysis.InnerProductSpace.TensorProduct

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate TensorProduct

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def KFin : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ l : X.Hs → Wp, IsMultOneMap D X l → (∃ v ∈ Vfl X, l v ≠ 0) →
      ∃ v₀ ∈ Vfl X, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) X.σ v₀ ∧ l v₀ ≠ 0

def NormForm : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ d : ℝ, IsFdegG D X d → ∀ ν : Measure (Mt k r),
      Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν → ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, ∀ ξ : Wp,
        Formalism.MainNotions.S.l2SG (k := k) (r := r) ν (fun g => beOp D X (X.σ g u) v ξ) =
          ENNReal.ofReal (‖u‖ ^ 2 / d * (⟪ξ, beOp D X v v ξ⟫_ℂ).re)

def SIntPh : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq),
    (∀ b : ℝ, AB k r ≤ b →
      Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) (D.μW.prod D.μN) ∧
      Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) (D.μW'.prod D.μN)) ∧
    ∀ (X : SigData k r) (d : ℝ), SqIntG D X → IsFdegG D X d → aM k r ≤ X.a →
      ∀ (P P' : X.Hs →L[ℂ] Wp) (Q Q' : Wq →L[ℂ] X.Hs),
        (∀ y, Q y ∈ Vfl X) → (∀ y, Q' y ∈ Vfl X) →
        (∀ x : Wp, ∃ u ∈ Vfl X, ∀ v, ⟪x, P v⟫_ℂ = ⟪u, v⟫_ℂ) →
        (∀ x : Wp, ∃ u ∈ Vfl X, ∀ v, ⟪x, P' v⟫_ℂ = ⟪u, v⟫_ℂ) →
        Integrable (Ph D (fun g => P.comp ((X.σ g).comp Q)) (fun g => P'.comp ((X.σ g).comp Q'))) D.μSS

def ScaleMove : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c μ : ℂ), inWb k r z → μ ≠ 0 →
    ∃ t : Mat k r, t ∈ GV k r ∧ t⁻¹ ∈ GV k r ∧ t * t⁻¹ = 1 ∧
      (∀ h ∈ UWset k r z, t * h = h * t) ∧
      (∀ m ∈ Nset k r, t * m * t⁻¹ ∈ Nset k r ∧ t⁻¹ * m * t ∈ Nset k r ∧
        psi k r z c (t * m * t⁻¹) = psi k r z (c * μ) m) ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Wp : Type) [NormedAddCommGroup Wp]
        [InnerProductSpace ℂ Wp] (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Wp →L[ℂ] Wp)) (B : H → Wp),
        Formalism.MainNotions.S.IsURepOn (GV k r) σ →
        (∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, σ t v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ) ∧
        (Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z (psi k r z c) σ π B →
          Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z (psi k r z (c * μ)) σ π (fun v => B (σ t v))) ∧
        ∀ ν : Measure (Mt k r), ν {x | Matrix.of x ∉ GV k r} = 0 → L2BoundedOnSmooth ν σ B →
          L2BoundedOnSmooth (ν.map fun x : Mt k r => fun i j => (t⁻¹ * Matrix.of x * t) i j) σ (fun v => B (σ t v))

def BeNzCore : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X → aM k r ≤ X.a →
    (∀ v : X.Hs, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) X.σ v →
      v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) X.σ) →
    (∀ u ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) X.σ, ∀ v : X.Hs,
      Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) X.σ v → beOp D X u v = 0) →
    ∀ (E : Submodule ℂ X.Hs) (B : X.Hs →ₗ[ℂ] Wp) (ν : Measure (Mt k r)),
      Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν → Dense (E : Set X.Hs) → X.w ∈ E →
      (∀ g ∈ GV k r, ∀ v ∈ E, X.σ g v ∈ E) →
      (∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ v ∈ E, B (X.σ (m * h) v) = psiD D m • D.π h (B v)) →
      (∀ v ∈ E, ContinuousOn (fun g => B (X.σ g v)) (GV k r)) →
      (∃ C : ℝ, ∀ v ∈ E, ∫⁻ x : Mt k r, ‖B (X.σ (Matrix.of x) v)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (C * ‖v‖ ^ 2)) →
      ∀ g ∈ GV k r, B (X.σ g X.w) = 0

def BesselIsometryScalar : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ l : X.Hs → Wp, IsMultOneMap D X l → ∀ d : ℝ, IsFdegG D X d →
      ∀ (E : Submodule ℂ X.Hs) (B : X.Hs →ₗ[ℂ] Wp) (ν : Measure (Mt k r)),
        Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν → Dense (E : Set X.Hs) → X.w ∈ E →
        (∀ g ∈ GV k r, ∀ v ∈ E, X.σ g v ∈ E) →
        (∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ v ∈ E, B (X.σ (m * h) v) = psiD D m • D.π h (B v)) →
        (∀ v ∈ E, ContinuousOn (fun g => B (X.σ g v)) (GV k r)) →
        (∀ v ∈ E, ∫⁻ x : Mt k r, ‖B (X.σ (Matrix.of x) v)‖ₑ ^ 2 ∂ν = ENNReal.ofReal (‖v‖ ^ 2)) →
        (∃ v ∈ Vfl X, l v ≠ 0) ∧ ∃ c : ℂ, ‖c‖ ^ 2 = d ∧ ∀ v ∈ E, v ∈ Vfl X → B v = c • l v

def MFixParam : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ l : X.Hs → Wp, IsMultOneMap D X l → ∀ d : ℝ, IsFdegG D X d →
      ∀ (Y : Type) (W' : Mat k r → Y → Wp ⊗[ℂ] Wq),
        (∀ y, AEStronglyMeasurable (fun g : Mt k r => W' (Matrix.of g) y) D.μG) →
        (∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ x ∈ GV k r, ∀ y,
          W' (m * h * x) y = psiD D m • TensorProduct.map (D.π h : Wp →ₗ[ℂ] Wp) LinearMap.id (W' x y)) →
        (∀ y, ∀ x ∈ GV k r,
          Integrable (fun g : Mt k r => gN (x⁻¹ * Matrix.of g) ^ (-X.a) * ‖W' (Matrix.of g) y‖) D.μG) →
        ∃ c : Y → Wq, ∀ y, ∀ x ∈ GV k r,
          ∫ g : Mt k r, ((d : ℂ) * star (mc X X.w X.w (Matrix.of g))) • W' (x * Matrix.of g) y ∂D.μG =
            l (X.σ x X.w) ⊗ₜ[ℂ] c y

def StBeKD : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X → aM k r ≤ X.a →
    ∀ d : ℝ, IsFdegG D X d → ∀ (B : X.Hs → Wp) (ν : Measure (Mt k r)),
      Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν →
      X.w ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) X.σ →
      Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) D.z (psi k r D.z cStd) X.σ D.π B →
      (∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) X.σ,
        Formalism.MainNotions.S.l2SG (k := k) (r := r) ν (fun g => B (X.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2)) →
      ∀ w ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) X.σ, w ∈ Vfl X →
      ∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) X.σ, v ∈ Vfl X →
        Integrable (beInt D X w v) (D.μW.prod D.μN) ∧ beOp D X w v = ((d : ℂ)⁻¹) • rk1 (B w) (B v)

def StBeK : Prop :=
  ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (B : L.Hs → L.Wp) (μG ν : Measure (Mt k r)) (a d : ℝ),
    1 ≤ k → L.c ≠ 0 → 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ a → 0 < d →
    Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG → Formalism.MainNotions.S.IsHaarOn (Nset k r) L.μN →
    Formalism.MainNotions.S.IsQuotMeas μG
      ((L.μW.prod L.μN).map (fun p : Mt k r × Mt k r => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)) ν →
    (∀ v w v' w' : L.Hs,
      Integrable (fun x : Mt k r => ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x : Mt k r, ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ ∂μG =
        ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) →
    (∀ v v' : L.Hs, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) L.σ v → Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) L.σ v' →
      ∃ C : ℝ, ∀ x ∈ UH (Hpk k r), ‖⟪v', L.σ x v⟫_ℂ‖ ≤ C * gN x ^ (-a)) →
    (∃ w₀ : L.Hs, w₀ ≠ 0 ∧ w₀ ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) L.σ ∧
      Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) L.σ w₀) →
    Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B →
    (∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) L.σ,
      Formalism.MainNotions.S.l2SG (k := k) (r := r) ν (fun g => B (L.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2)) →
    ∀ w ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) L.σ, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) L.σ w →
    ∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) L.σ, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) L.σ v →
      Integrable (fun p : Mt k r × Mt k r =>
        (⟪v, L.σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r L.z L.c (Matrix.of p.2))) •
          L.π (Matrix.of p.1)⁻¹) (L.μW.prod L.μN) ∧
      ∫ p : Mt k r × Mt k r,
        (⟪v, L.σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r L.z L.c (Matrix.of p.2))) •
          L.π (Matrix.of p.1)⁻¹ ∂(L.μW.prod L.μN) =
        (innerSL ℂ ((((Real.sqrt d)⁻¹ : ℝ) : ℂ) • B v)).smulRight ((((Real.sqrt d)⁻¹ : ℝ) : ℂ) • B w)

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down
