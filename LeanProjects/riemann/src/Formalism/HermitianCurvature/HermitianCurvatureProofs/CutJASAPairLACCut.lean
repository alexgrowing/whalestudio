import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLExh

open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ACProper : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (C C' : Set (B.Mat k r)),
    IsCompact C → IsCompact C' → C' ⊆ JF.Om k r D.z D.z' →
    ∃ P : Set (B.SS k r), IsCompact P ∧ ∀ p, D.inSS p → ∀ g ∈ C', B.sgs p g ∈ C → p ∈ P

def ACBump : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (K : Set ((Fin r → ℂ) × ℂ)),
    IsCompact K → K ⊆ JF.QDom k r D.z D.z' →
    ∃ φ₀ : B.Mat k r → ℝ, ContDiff ℝ ∞ φ₀ ∧ (∀ g, 0 ≤ φ₀ g) ∧ HasCompactSupport φ₀ ∧
      tsupport φ₀ ⊆ Q.OmPlus k r D.z D.z' ∧ ∀ q ∈ K, 0 < φ₀ (B.gq D q)

def ACInv : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (φ₀ : B.Mat k r → ℝ), Continuous φ₀ →
    ∀ p₀, D.inSS p₀ → ∀ g : B.Mat k r, ∫ p, φ₀ (B.sgs p (B.sgs p₀ g)) ∂D.μSS = ∫ p, φ₀ (B.sgs p g) ∂D.μSS

def ACInt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (φ₀ : B.Mat k r → ℝ), Continuous φ₀ → HasCompactSupport φ₀ →
    ∀ g ∈ JF.Om k r D.z D.z', Integrable (fun p => φ₀ (B.sgs p g)) D.μSS

def ACHaarPos : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (O : Set (B.SS k r)), IsOpen O → oneP ∈ O → 0 < D.μSS O

def ACSmooth : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (φ₀ : B.Mat k r → ℝ),
    ContDiff ℝ ∞ φ₀ → HasCompactSupport φ₀ → tsupport φ₀ ⊆ Q.OmPlus k r D.z D.z' →
    ∀ g₀ ∈ JF.Om k r D.z D.z', ∃ (U : Set (B.Mat k r)) (I' : B.Mat k r → ℝ), IsOpen U ∧ g₀ ∈ U ∧
      ContDiffOn ℝ ∞ I' U ∧ ∀ g ∈ U, g ∈ B.GV k r → ∫ p, φ₀ (B.sgs p g) ∂D.μSS = I' g

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
