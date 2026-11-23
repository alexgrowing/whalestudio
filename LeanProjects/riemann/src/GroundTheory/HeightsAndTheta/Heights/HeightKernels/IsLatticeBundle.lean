import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

abbrev ProjFunField (K : Type) [Field K] (i : ℕ) : Type := FractionRing (MvPolynomial (Fin (i - 1)) K)

def projCoord (K : Type) [Field K] (i : ℕ) (j : Fin i) : ProjFunField K i :=
  if h : (j : ℕ) = 0 then 1
  else algebraMap (MvPolynomial (Fin (i - 1)) K) (ProjFunField K i) (X ⟨(j : ℕ) - 1, by omega⟩)

abbrev OKBlock (d i : ℕ) : Unit → Type := fun _ => Fin d × Fin i

def okPoint (K : Type) [Field K] [NumberField K] {d : ℕ} (i : ℕ) (ω : Module.Basis (Fin d) ℤ (𝓞 K)) :
    (Σ _ : Unit, Fin d × Fin i) → ProjFunField K i :=
  fun p => algebraMap K (ProjFunField K i) (ω p.2.1 : K) * projCoord K i p.2.2

def pointOver {K : Type} [Field K] [NumberField K] {d i : ℕ} (ω : Module.Basis (Fin d) ℤ (𝓞 K))
    (σ : K →+* ℂ) (w : Fin i → ℂ) : (Σ _ : Unit, Fin d × Fin i) → ℂ :=
  fun p => σ (ω p.2.1 : K) * w p.2.2

def latticeNorm {K : Type} [Field K] [NumberField K] {i : ℕ}
    (hm : GroundTheory.Heights₂.Heights.HermitianMetric K (Fin i → 𝓞 K)) (σ : K →+* ℂ) (w : Fin i → ℂ) : ℝ :=
  Real.sqrt ((hm.form σ).inner
    ((GroundTheory.Heights₂.Heights.standardCoord K σ (Fin i)).symm (WithLp.toLp 2 w))
    ((GroundTheory.Heights₂.Heights.standardCoord K σ (Fin i)).symm (WithLp.toLp 2 w))).re

def IsLatticeBundle {K : Type} [Field K] [NumberField K] {d i : ℕ}
    (ω : Module.Basis (Fin d) ℤ (𝓞 K)) (hm : GroundTheory.Heights₂.Heights.HermitianMetric K (Fin i → 𝓞 K))
    (A : HermLine (OKBlock d i)) : Prop :=
  A.a = 1 ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧
    ∀ (σ : K →+* ℂ) (w : Fin i → ℂ), w ≠ 0 → A.h (pointOver ω σ w) = latticeNorm hm σ w

def freeBundle {K : Type} [Field K] [NumberField K] {i : ℕ}
    (hm : GroundTheory.Heights₂.Heights.HermitianMetric K (Fin i → 𝓞 K)) :
    GroundTheory.Heights₂.Heights.HermitianBundle.{0} K :=
  ⟨Fin i → 𝓞 K, hm⟩

def S7.Statement : Prop :=
  SuccessiveMinimaLowerBound →
  ∀ (K : Type) [Field K] [NumberField K] (d i : ℕ) (ω : Module.Basis (Fin d) ℤ (𝓞 K))
    (hm : GroundTheory.Heights₂.Heights.HermitianMetric K (Fin i → 𝓞 K)) (A : HermLine (OKBlock d i))
    (ε : ℝ) (II : IntersectionSystem),
    1 ≤ i → 0 < ε → IsLatticeBundle ω hm A → IsIntersectionSystem II →
    IsArithVar (mCoordIdeal (okPoint K i ω)) i ∧ Birational (okPoint K i ω) ∧
    ∃ W : Ideal (MRing (OKBlock d i)), IsArithVar W 1 ∧ mCoordIdeal (okPoint K i ω) ≤ W ∧
      -II Unit (OKBlock d i) W 1 ![A] / degC W ≤
        -(freeBundle hm).slope ⊤ + 1 / 2 * Real.log i + ε

abbrev GrBlock (f N j : ℕ) : Fin f → Type := fun _ => {I : Finset (Fin N) // I.card = j}

abbrev GrFunField (f N j : ℕ) : Type := FractionRing (MvPolynomial (Fin f × Fin j × Fin (N - j)) ℚ)

def grMatrix (f N j : ℕ) (τ : Fin f) : Matrix (Fin j) (Fin N) (GrFunField f N j) :=
  fun a c => if h : (c : ℕ) < j then (if (c : ℕ) = a then 1 else 0)
    else algebraMap (MvPolynomial (Fin f × Fin j × Fin (N - j)) ℚ) (GrFunField f N j)
      (X ((τ, a, ⟨(c : ℕ) - j, by omega⟩) : Fin f × Fin j × Fin (N - j)))

def grPoint (f N j : ℕ) : (Σ τ : Fin f, GrBlock f N j τ) → GrFunField f N j :=
  fun p => (Matrix.of fun a b : Fin j => grMatrix f N j p.1 a (p.2.1.orderEmbOfFin p.2.2 b)).det

def grFS (f N j : ℕ) : HermLine (GrBlock f N j) := HermLine.sqMetric 1

def MirabolicColumnBlock.Statement : Prop :=
  SuccessiveMinimaUpperBound →
  ∀ (f N j : ℕ) (II : IntersectionSystem), 1 ≤ f → j ≤ N → IsIntersectionSystem II →
    IsArithVar (mCoordIdeal (grPoint f N j)) (f * j * (N - j) + 1) ∧
    II (Fin f) (GrBlock f N j) (mCoordIdeal (grPoint f N j)) (f * j * (N - j) + 1)
        (fun _ => grFS f N j) ≤
      ((f * j * (N - j) + 1 : ℕ) : ℝ) * ((f * j : ℕ) / 2 * Real.log (N + 1)) *
        geomDeg (mCoordIdeal (grPoint f N j)) (grFS f N j) (f * j * (N - j))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
