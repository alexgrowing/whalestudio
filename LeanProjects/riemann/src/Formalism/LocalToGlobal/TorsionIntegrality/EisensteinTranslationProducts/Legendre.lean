import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def ZetaSummable : Prop :=
  ∀ (L : PeriodPair) (z : ℂ),
    Summable (fun l : L.lattice => 1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)

def ZetaHasDeriv : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → HasDerivAt (wZeta L) (-(L.weierstrassP z)) z

def ZetaOdd : Prop := ∀ (L : PeriodPair) (z : ℂ), wZeta L (-z) = -wZeta L z

def ZetaPole : Prop :=
  ∀ L : PeriodPair, Filter.Tendsto (fun z => wZeta L z - 1 / z) (nhdsWithin 0 {0}ᶜ) (nhds 0)

def ZetaQuasi : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice → z ∉ L.lattice → wZeta L (z + ω) = wZeta L z + wEta L ω

def SigmaSummable : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), Summable (fun l : L.lattice => ‖wFactor (l : ℂ) z - 1‖)

def SigmaProdLU : Prop :=
  ∀ L : PeriodPair, HasProdLocallyUniformlyOn (fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z)
    (fun z => ∏' l : L.lattice, wFactor (l : ℂ) z) Set.univ

def SigmaEntire : Prop := ∀ L : PeriodPair, Differentiable ℂ (wSigma L)

def SigmaOdd : Prop := ∀ (L : PeriodPair) (z : ℂ), wSigma L (-z) = -wSigma L z

def SigmaZero : Prop := ∀ (L : PeriodPair) (z : ℂ), wSigma L z = 0 ↔ z ∈ L.lattice

def SigmaSimple : Prop :=
  ∀ L : PeriodPair, deriv (wSigma L) 0 = 1 ∧ ∀ z ∈ L.lattice, deriv (wSigma L) z ≠ 0

def SigmaLogDeriv : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → HasDerivAt (wSigma L) (wZeta L z * wSigma L z) z

def SigmaLogDeriv2 : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice →
    wSigma L z * iteratedDeriv 2 (wSigma L) z - deriv (wSigma L) z ^ 2
      = -(L.weierstrassP z) * wSigma L z ^ 2

def SigmaQuasi : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice →
    wSigma L (z + ω) = semiChar L ω * Complex.exp (wEta L ω * (z + ω / 2)) * wSigma L z

def EtaEisenstein : Prop :=
  ∀ L : PeriodPair,
    wEta L L.ω₁ = L.ω₁ * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 ∧
    wEta L L.ω₂ = L.ω₂ * ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2

def Legendre : Prop :=
  ∀ L : PeriodPair,
    wEta L L.ω₁ * L.ω₂ - wEta L L.ω₂ * L.ω₁
      = (if 0 < (L.ω₂ / L.ω₁).im then 1 else -1) * (2 * (Real.pi : ℂ) * Complex.I)

end Formalism.L2.Th1.F
