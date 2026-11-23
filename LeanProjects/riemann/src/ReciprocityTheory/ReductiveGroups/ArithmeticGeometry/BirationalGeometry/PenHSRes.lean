import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter

def HeightBoundResolution : Prop :=
  ResExistsStatement → ResBridgeStatement → ∀ (ι0 : Type) [Fintype ι0] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (x : ι0 → Ω) (D : ℕ)
    (A : HermLine (fun _ : Unit => ι0))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → A.a = 1 →
    IsArithVar (mCoordIdeal (fun p : Σ _ : Unit, ι0 => x p.2)) (D + 1) →
    Birational (fun p : Σ _ : Unit, ι0 => x p.2) →
    IsSemipositiveH (mCoordIdeal (fun p : Σ _ : Unit, ι0 => x p.2)) A → IsConjInvariantH A →
    II Unit (fun _ => ι0) (mCoordIdeal (fun p : Σ _ : Unit, ι0 => x p.2)) (D + 1) (fun _ => A) ≤
      liminf (fun τ : ℕ =>
        smallSectionCount (IsSmallH (mCoordIdeal (fun p : Σ _ : Unit, ι0 => x p.2)) (fun p => x p.2) A)
          (fun τ => secM (fun p : Σ _ : Unit, ι0 => x p.2) (fun _ => τ)) τ /
          ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop

def SuccessiveMinimaResolution : Prop :=
  ResExistsStatement → ResBridgeStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι)
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSemipositiveH (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤
      arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D

end ReciprocityTheory.ChartRestriction.G.Geo
