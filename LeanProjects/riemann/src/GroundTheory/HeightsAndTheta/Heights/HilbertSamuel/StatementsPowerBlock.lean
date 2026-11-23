import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsBoundedAtOfIsBoundedH
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable (ι) in

def addIdx (N : ℕ) : Option K → Type := fun k => Option.elim k (Fin N) ι

instance addIdx.instFintype (N : ℕ) : ∀ k, Fintype (addIdx ι N k)
  | none => inferInstanceAs (Fintype (Fin N))
  | some k => inferInstanceAs (Fintype (ι k))

def addBlock {Ω : Type} (y : (Σ k, ι k) → Ω) {N : ℕ} (v : Fin N → Ω) : (Σ k, addIdx ι N k) → Ω
  | ⟨none, j⟩ => v j
  | ⟨some k, i⟩ => y ⟨k, i⟩

def basePart₂ {N : ℕ} (z : (Σ k, addIdx ι N k) → ℂ) : (Σ k, ι k) → ℂ := fun p => z ⟨some p.1, p.2⟩

end Objects

def PowerBlockDatum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (m N : ℕ) (v : Fin N → Ω) (d : HSMBlockDatum D (Option K) (addIdx ι N) Ω)
      (μ : Measure ((Σ k, ι k) → ℂ)),
      1 ≤ m ∧ d.y = addBlock y v ∧ d.k₀ = none ∧
      (∀ j, v j ∈ chartLat y A.a m) ∧ KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v ∧
      (∀ z ∈ mcPts (mCoordIdeal d.y), ∀ j : Fin N,
        secNormAt y A m (v j) (basePart₂ z) * d.A.h z = ‖z ⟨none, j⟩‖) ∧
      (∀ᶠ q : ℕ in atTop, chartLat y A.a (m * q) = secM d.y (blockDeg (none : Option K) q)) ∧
      IsProbabilityMeasure μ ∧ μ (mcPts (mCoordIdeal y))ᶜ = 0 ∧ IsZariskiDenseMeasure (mCoordIdeal y) μ ∧
      ∀ (q : ℕ) (f : MRing (addIdx ι N)), IsMultiHomog f (blockDeg (none : Option K) q) →
        sectionL2Norm μ y A (m * q) (aeval d.y f) = blockL2Norm d q f

def PowerBlockTop.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (m N : ℕ) (v : Fin N → Ω) (B : HermLine (addIdx ι N))
    (I : AllFam),
    I.IsFamily → IsArithVar (mCoordIdeal y) (D + 1) → IsSmoothHerm A → 1 ≤ m →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    B.a = unitDeg (none : Option K) → IsSmoothHerm B →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    I (Option K) (addIdx ι N) (mCoordIdeal (addBlock y v)) (D + 1) (fun _ => B) =
      (m : ℝ) ^ (D + 1) * I K ι (mCoordIdeal y) (D + 1) (fun _ => A)

def BlockChiCovolume.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n : ℕ) (E : AddSubgroup Ω), E = secM d.y (blockDeg d.k₀ n) →
    ∀ (r : ℕ) (ψ : E →+ EuclideanSpace ℝ (Fin r)), Function.Injective ψ →
      (∀ (s : E) (f : MRing ι), IsMultiHomog f (blockDeg d.k₀ n) → aeval d.y f = (s : Ω) →
        ‖ψ s‖ = blockL2Norm d n f) →
      ∀ [DiscreteTopology (imageLattice ψ)] [IsZLattice ℝ (imageLattice ψ)],
        -Real.log (ZLattice.covolume (imageLattice ψ)) = blockChi d n

open ProjLine

namespace PowerBlockProjectiveLine

def projectiveLineCoordinates : Fin 2 → FnField := fun j => y ⟨(), j⟩

def fsNew : HermLine (addIdx (GlobalTheory (Fin 2)) 2) :=
  HermLine.ofMetrics (fun k => fsMetric (addIdx (GlobalTheory (Fin 2)) 2 k)) (unitDeg (none : Option Unit))

theorem minor_mem :
    (X ⟨some (), (0 : Fin 2)⟩ * X ⟨none, (1 : Fin 2)⟩ - X ⟨some (), (1 : Fin 2)⟩ * X ⟨none, (0 : Fin 2)⟩ :
      MRing (addIdx (GlobalTheory (Fin 2)) 2)) ∈ mCoordIdeal (addBlock y projectiveLineCoordinates) := by
  show mConeMap (addBlock y projectiveLineCoordinates) _ = 0
  simp [mConeMap, addBlock, projectiveLineCoordinates, ProjLine.y]
  ring

end PowerBlockProjectiveLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
