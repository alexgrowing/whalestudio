import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def fT (L : PeriodPair) (t z : ℂ) : ℂ := opU L t (sgStar L) z / sgStar L z

def thetaZeroCharacter (L : PeriodPair) (ω₀ ω : ℂ) : ℂ :=
  semiChar L ω * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω ω₀ : ℂ))

def FtQuasi : Prop :=
  ∀ (L : PeriodPair) (t ω z : ℂ), ω ∈ L.lattice →
    fT L t (z + ω) = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE L ω t : ℂ)) * fT L t z

def FtPow : Prop :=
  ∀ (L : PeriodPair) (t : ℂ) (N : ℕ), (N : ℂ) * t ∈ L.lattice → IsPeriodic L (fun z => fT L t z ^ N)

def FtOrder : Prop :=
  ∀ (L : PeriodPair) (t z : ℂ), t ∉ L.lattice →
    MeromorphicAt (fT L t) z ∧ meromorphicOrderAt (fT L t) z
      = (by classical exact if z + t ∈ L.lattice then 1 else if z ∈ L.lattice then -1 else 0)

def FtInv : Prop :=
  ∀ (L : PeriodPair) (t z : ℂ), z ∉ L.lattice → z - t ∉ L.lattice → fT L t (-z) * fT L t (z - t) = 1

def FtDouble : Prop :=
  ∀ (L : PeriodPair) (y z : ℂ), z ∉ L.lattice → z + y ∉ L.lattice →
    fT L (2 * y) z = fT L y (z + y) * fT L y z

def OpUTh0 : Prop :=
  ∀ (L : PeriodPair) (t x z : ℂ),
    opU L x (th0 L t) z
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L x t : ℂ)) * opU L (x + t) (sgStar L) z
        / opU L t (sgStar L) 0

def ThetaZeroTranslateProduct : Prop :=
  ∀ (L : PeriodPair) (t P Q z : ℂ), Q ∉ L.lattice → z + P + t ∉ L.lattice →
    opU L (P + Q) (th0 L t) z * opU L (P - Q) (th0 L t) z
      = opU L Q (sgStar L) 0 ^ 2 * (L.weierstrassP Q - L.weierstrassP (z + P + t))
        * opU L P (th0 L t) z ^ 2

def ThetaZeroCube : Prop :=
  ∀ (L : PeriodPair) (ω₀ b c : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    IsPeriodic L (fun a =>
      th0 L (ω₀ / 2) (a + b + c) * th0 L (ω₀ / 2) a * th0 L (ω₀ / 2) b * th0 L (ω₀ / 2) c
        / (th0 L (ω₀ / 2) (a + b) * th0 L (ω₀ / 2) (b + c) * th0 L (ω₀ / 2) (c + a)))

def ThetaZeroSecond : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    deriv (th0 L (ω₀ / 2)) 0 = 0 ∧
    iteratedDeriv 2 (th0 L (ω₀ / 2)) 0 = -(L.weierstrassP (ω₀ / 2) + s2 L)

def ThetaZeroLine : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (F : ℂ → ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice → Differentiable ℂ F →
    (∀ ω ∈ L.lattice, ∀ z, F (z + ω) = thetaZeroCharacter L ω₀ ω
      * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * F z) →
    ∀ z, F z = F 0 * th0 L (ω₀ / 2) z

def IsFibreReps (L : PeriodPair) (α t : ℂ) (T : Finset ℂ) : Prop :=
  (∀ Q ∈ T, α * Q - t ∈ L.lattice ∧ 2 * Q ∉ L.lattice) ∧
  (∀ Q ∈ T, ∀ Q' ∈ T, (Q - Q' ∈ L.lattice ∨ Q + Q' ∈ L.lattice) → Q = Q') ∧
  (∀ z, α * z - t ∈ L.lattice → ∃ Q ∈ T, z - Q ∈ L.lattice ∨ z + Q ∈ L.lattice)

def FibreRepsExist : Prop :=
  ∀ (L : PeriodPair) (α t : ℂ), α ≠ 0 → MulStable L α → 2 * t ∈ L.lattice →
    (∀ z, α * z - t ∈ L.lattice → 2 * z ∉ L.lattice) → ∃ T : Finset ℂ, IsFibreReps L α t T

def Th0Isogeny : Prop :=
  ∀ (L : PeriodPair) (α ω₀ : ℂ) (T : Finset ℂ), α ≠ 0 → MulStable L α → ω₀ ∈ L.lattice →
    ω₀ / 2 ∉ L.lattice → IsFibreReps L α (ω₀ / 2) T →
    (∀ ω ∈ L.lattice, thetaZeroCharacter L ω₀ (α * ω) = thetaZeroCharacter L ω₀ ω ^ (2 * T.card)) →
    (2 * (T.card : ℝ) = Complex.normSq α) ∧
    ∀ z, z ∉ L.lattice → z - ω₀ / 2 ∉ L.lattice →
      th0 L (ω₀ / 2) (α * z) * (L.weierstrassP z - L.weierstrassP (ω₀ / 2)) ^ T.card
        = th0 L (ω₀ / 2) z ^ (2 * T.card) * ∏ Q ∈ T, (L.weierstrassP z - L.weierstrassP Q)

end Formalism.L2.Th1.F
