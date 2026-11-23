import Formalism.MoebiusJetDuality.Statement

noncomputable section

namespace Formalism.MJ

open MvPolynomial

universe u v

def EvDualJet : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (A : Subring R) (F : MvPolynomial σ R),
    (∀ P : MvPolynomial σ R, IsIntegralJet A P → evOp P F ∈ A) ↔
      ∀ α, (mfac α : R) * coeff α F ∈ A

def EvDualOp : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (A : Subring R) (P : MvPolynomial σ R),
    (∀ F : MvPolynomial σ R, IsIntegralJet A F → evOp P F ∈ A) ↔
      ∀ α, (mfac α : R) * coeff α P ∈ A

def EvKernel : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (F : MvPolynomial σ R),
    (∀ P : MvPolynomial σ R, evOp P F = 0) ↔ ∀ α, (mfac α : R) * coeff α F = 0

def EvSymm : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (P F : MvPolynomial σ R), evOp P F = evOp F P

def EvLinear : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (c : R) (P F G : MvPolynomial σ R),
    evOp P (c • F + G) = c * evOp P F + evOp P G

def EvDegree : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (P F : MvPolynomial σ R) (m n : ℕ),
    P.IsHomogeneous m → F.IsHomogeneous n → m ≠ n → evOp P F = 0

end Formalism.MJ
