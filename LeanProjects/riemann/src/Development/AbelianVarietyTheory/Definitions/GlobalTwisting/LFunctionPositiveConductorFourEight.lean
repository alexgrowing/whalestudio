import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Formalism.LandauZeroFreeBounds.Statement
import Formalism.FrobeniusOrbits.Statement

noncomputable section

namespace GlobalTheory.NT

open Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField IsDedekindDomain ArithmeticFunction
open Formalism.HermitianLattices.GL2PrimeSums (Li PP)

def ZeroFreeRegionPrimitiveCharacter : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ q → χ.IsPrimitive →
    ∀ s : ℂ, 1 - c / Real.log (max (q : ℝ) (q * |s.im|)) ≤ s.re → DirichletCharacter.LFunction χ s = 0 →
      IsRealChar χ ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧
      ∀ s' : ℂ, 1 - c / Real.log (max (q : ℝ) (q * |s'.im|)) ≤ s'.re → DirichletCharacter.LFunction χ s' = 0 → s' = s

def PageTheorem : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (β₁ β₂ : ℝ), χ₁.IsPrimitive → χ₂.IsPrimitive → IsRealChar χ₁ → IsRealChar χ₂ →
    (q₁ : ℝ) ≤ Q → (q₂ : ℝ) ≤ Q → 1 - c / Real.log Q < β₁ → β₁ < 1 → 1 - c / Real.log Q < β₂ → β₂ < 1 →
    DirichletCharacter.LFunction χ₁ β₁ = 0 → DirichletCharacter.LFunction χ₂ β₂ = 0 →
    q₁ = q₂ ∧ ∀ n : ℕ, χ₁ (n : ZMod q₁) = χ₂ (n : ZMod q₂)

def ZetaClassicalZeroFreeRegion : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3)

def LFunctionPositive_conductorFourEight : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q = 4 ∨ q = 8) → χ.IsPrimitive → ∀ σ : ℝ, 0 < σ →
    0 < (DirichletCharacter.LFunction χ σ).re ∧ (DirichletCharacter.LFunction χ σ).im = 0

def QE : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u →
    ‖psi0 χ u + zsum χ {ρ | |ρ.im| < T} (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤
      C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ {ρ | |ρ.im| < 1} (fun ρ => 1 / ‖ρ‖))

def QF : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ,
    (ntZeros χ ∩ {ρ | |ρ.im - t| ≤ 1}).Finite ∧
      zsumR χ {ρ | |ρ.im - t| ≤ 1} (fun _ => 1) ≤ C * Real.log (q * (|t| + 2))

def QFsum : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T →
    (ntZeros χ ∩ {ρ | |ρ.im| ≤ T}).Finite ∧
      zsumR χ {ρ | 1 < |ρ.im| ∧ |ρ.im| < T} (fun ρ => 1 / |ρ.im|) ≤ C * Real.log (q * T) ^ 2

def QFsym : Prop :=
  (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ ρ : ℂ,
    (ρ ∈ ntZeros χ ↔ 1 - ρ ∈ ntZeros χ⁻¹) ∧ (ρ ∈ ntZeros χ ↔ 1 - (starRingEnd ℂ) ρ ∈ ntZeros χ) ∧
    (ρ ∈ ntZeros χ → mult χ⁻¹ (1 - ρ) = mult χ ρ ∧ mult χ (1 - (starRingEnd ℂ) ρ) = mult χ ρ ∧ 1 ≤ mult χ ρ)) ∧
  ∀ σ : ℝ, 0 < σ → σ < 1 → (riemannZeta σ).re < 0 ∧ (riemannZeta σ).im = 0

def QG : Prop :=
  (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n ≤ 2 * y) ∧
  (∀ y : ℝ, 2 ≤ y → (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ 2 * y / Real.log y) ∧
  (∀ y : ℝ, 2 ≤ y → Chebyshev.theta y < y * Real.log 4) ∧
  (∃ c : ℝ, 0 < c ∧ ∀ y : ℝ, 2 ≤ y → c * y ≤ Chebyshev.theta y) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → |∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) - Real.log y| ≤ C)

def QC : Prop :=
  ∀ e : ℝ, 0 < e → ∃ c : ℝ, 0 < c ∧ ∀ σ Q : ℝ, 4 / 5 ≤ σ → σ ≤ 1 → 3 ≤ Q →
    ∑ q ∈ Finset.range ⌊Q⌋₊, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive},
      zsumR χ {ρ | σ ≤ ρ.re ∧ |ρ.im| ≤ Q} (fun _ => 1) ≤ c * Q ^ ((6 + e) * (1 - σ))

def QA : Prop :=
  ∃ c₂ c₃ C : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L],
      2 ≤ bigQ K L → ∃ (θ : (L ≃ₐ[K] L) → ℝ) (β : ℝ),
        (((∀ σ, θ σ = 0) ∧ ∀ (χ : (L ≃ₐ[K] L) →* ℂˣ) (b : ℝ), χ ^ 2 = 1 → 1 - 1 / (8 * Real.log (bigQ K L)) < b → b < 1 →
            ¬ HeckeZero L χ b) ∨
          ∃ χ₁ : (L ≃ₐ[K] L) →* ℂˣ, χ₁ ^ 2 = 1 ∧ 1 - 1 / (8 * Real.log (bigQ K L)) < β ∧ β < 1 ∧ HeckeZero L χ₁ β ∧
            ∀ σ, (θ σ : ℂ) = (χ₁ σ : ℂˣ)) ∧
        ∀ (σ : L ≃ₐ[K] L) (X : ℝ), bigQ K L ^ c₂ ≤ X →
          |(Module.finrank K L : ℝ) * piC L σ X - (Li X - θ σ * Li (X ^ β))| ≤
            C * (Real.exp (-(c₃ * Real.log X / Real.log (bigQ K L))) +
              Real.exp (-(Real.sqrt (c₃ * Real.log X) / Real.sqrt (Module.finrank ℚ K)))) * (Li X - θ σ * Li (X ^ β))

def QB : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L],
    2 ≤ bigQ K L → ∀ (χ : (L ≃ₐ[K] L) →* ℂˣ) (β : ℝ), χ ^ 2 = 1 → β < 1 → HeckeZero L χ β →
      c / bigQ K L ^ 2 ≤ (1 - β) * Real.log (bigQ K L)

def RayField : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) ∧
      Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ IsFrob L 𝔭 σ} = ⊤ ∧
      ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
        ((∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) ↔
          ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α})

def QAQ : Prop :=
  ∃ c₂ c₃ C : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧ ∀ (m : ℕ) [NeZero m], 3 ≤ m → m % 4 ≠ 2 → ∃ (θ : ℕ → ℝ) (β : ℝ),
    ((∀ a, θ a = 0) ∨ ∃ χ₁ : DirichletCharacter ℂ m, χ₁ ≠ 1 ∧ IsRealChar χ₁ ∧ 1 - 1 / (8 * Real.log m) < β ∧ β < 1 ∧
        DirichletCharacter.LFunction χ₁ β = 0 ∧ ∀ a : ℕ, (θ a : ℂ) = χ₁ (a : ZMod m)) ∧
    ∀ a : ℕ, a.Coprime m → ∀ X : ℝ, (m : ℝ) ^ c₂ ≤ X →
      |(m.totient : ℝ) * (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])).card : ℝ) -
          (Li X - θ a * Li (X ^ β))| ≤
        C * (Real.exp (-(c₃ * Real.log X / Real.log m)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
          (Li X - θ a * Li (X ^ β))

def QBQ : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m) (β : ℝ), 3 ≤ m → χ ≠ 1 → IsRealChar χ → β < 1 →
    DirichletCharacter.LFunction χ β = 0 → c / (m : ℝ) ^ 2 ≤ (1 - β) * Real.log m

def PsiReg : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ M : ℝ, 8 ≤ M → (q : ℝ) ≤ M → (∀ ρ ∈ ntZeros χ, ρ.re ≤ 1 - c₀ / Real.log (M * (|ρ.im| + 3))) →
    ∀ u : ℝ, 3 ≤ u → ‖psi0 χ u‖ ≤ C * u * (Real.log u + Real.log M) ^ 2 *
      Real.exp (-(c * Real.log u / (Real.log M + Real.sqrt (Real.log u))))

def PNT : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ u : ℝ, 1 ≤ u → ‖psi0 χ u‖ ≤ C * u * Real.exp (-(c * Real.sqrt (Real.log u)))

def IntegralFormulaTwistedChebyshev : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ y : ℝ, 1 ≤ y →
    MeasureTheory.IntegrableOn (fun u : ℝ => psi0 χ u / (u : ℂ) ^ 2) (Set.Ioi y) ∧
      gChi χ y = -(y : ℂ) * ∫ u in Set.Ioi y, psi0 χ u / (u : ℂ) ^ 2

def WeightedSumTendsto : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ x : ℝ, 1 ≤ x →
    Filter.Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, ((GlobalTheoryTheory.cn x n : ℝ) : ℂ) * χ (n : ZMod q))
      Filter.atTop (nhds (-gChi χ x))

def FewBadRealCharacters : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q →
    (({c : Σ q : ℕ, DirichletCharacter ℂ (q + 1) | ((c.1 + 1 : ℕ) : ℝ) ≤ Q ∧ c.2.IsPrimitive ∧ IsRealChar c.2 ∧ c.2 ≠ 1 ∧
      ¬ GoodFor Q c.2}.ncard : ℕ) : ℝ) ≤ C * Q ^ ((1 : ℝ) / 4)

def ChebyshevPsiCharacterBounds : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → GoodFor Q χ →
    (∀ u : ℝ, 2 ≤ u → ‖psi0 χ u‖ ≤
      C * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2)) ∧
    ∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u → ‖psi0 χ u‖ ≤ C * u * Real.exp (-c * Real.sqrt (Real.log u))

def ChebyshevTailSmall : Prop :=
  ∃ C : ℝ, ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Q : ℝ,
    x ^ (eps / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (eps / 4) →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → GoodFor Q χ →
      (∃ S : ℂ, TailSum χ (zz x) S ∧ ‖(x : ℂ) * S‖ ≤ x ^ eps) ∧ ‖logDerivativeAtOne χ‖ ≤ 200 * eps * Real.log x + C

def QAK : Prop :=
  ∃ C₀ Cr cr cb : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < cb ∧ ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 1 ≤ M →
    ∃ (G β : ℝ) (θ : ℤ) (π₁ π₂ : ℝ → ℕ) (η' : ℝ → ℝ),
      1 ≤ G ∧ G ≤ 4 * d * (M : ℝ) ^ 2 ∧ θ ∈ ({-1, 0, 1} : Set ℤ) ∧
      (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / ((4 * d * (M : ℝ) ^ 2) ^ 2 * Real.log (4 * d * (M : ℝ) ^ 2)) ≤ 1 - β) ∧
      (∀ Y : ℝ, 1 ≤ Y → (π₂ Y : ℝ) ≤ 2 * Real.sqrt Y) ∧
      (∀ Y : ℝ, 0 ≤ η' Y ∧ η' Y ≤ 3 * Real.log (4 * d * (M : ℝ) ^ 2)) ∧
      (∀ Y : ℝ, (4 * d * (M : ℝ) ^ 2) ^ C₀ ≤ Y →
        |G * ((π₁ Y : ℝ) + π₂ Y + η' Y) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β Y| ≤
          Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr (4 * d * (M : ℝ) ^ 2) Y * Formalism.HermitianLattices.GL2PrimeSums.Emain θ β Y) ∧
      ∀ Y Y' : ℝ, 0 ≤ Y → Y ≤ Y' → (π₁ Y' : ℝ) - π₁ Y ≤
        2 * (({p : ℕ | p.Prime ∧ Y < p ∧ (p : ℝ) ≤ Y' ∧ NormOne d M p}.ncard : ℕ) : ℝ)

def NormPrimesShortIntervals : Prop :=
  ∃ C₀ C c c' : ℝ, 1 ≤ C₀ ∧ 0 < C ∧ 0 < c ∧ 0 < c' ∧ ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 1 ≤ M →
    ∀ X h : ℝ, (4 * d * (M : ℝ) ^ 2) ^ C₀ ≤ X → 0 < h → h ≤ 1 →
      Formalism.HermitianLattices.GL2PrimeSums.rhoErr C c (4 * d * (M : ℝ) ^ 2) X ≤ h / 100 →
      (4 * d * (M : ℝ) ^ 2) ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
      c' * h * (4 * d * (M : ℝ) ^ 2) ^ (-6 : ℝ) * X / Real.log X ≤
        (({p : ℕ | p.Prime ∧ X < p ∧ (p : ℝ) ≤ X * (1 + h) ∧ NormOne d M p}.ncard : ℕ) : ℝ)

def QuadraticSymbolMeans : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (m₀ a₀ : ℕ) (X : ℝ),
    0 < m₀ → 8 ∣ m₀ → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (eps / 5) ∨ zz x < p) → a₀.Coprime m₀ → a₀ % 4 = 3 →
    0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X →
    X ^ ((9 : ℝ) / 10) ≤ ((PP m₀ a₀ X).card : ℝ) ∧ ∃ nStar : ℕ,
      ∀ n n' : ℕ, n ∈ Finset.Icc 1 ⌊zz x⌋₊ → n' ∈ Finset.Icc 1 ⌊zz x⌋₊ → IsPrimePow n → IsPrimePow n' →
        Formalism.HermitianLattices.GL2PrimeSums.outPart m₀ (n * n') ≠ 1 → Formalism.HermitianLattices.GL2PrimeSums.outPart m₀ (n * n') ≠ nStar →
        |(∑ q ∈ PP m₀ a₀ X, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / (PP m₀ a₀ X).card| ≤
          C * Real.exp (-c * Real.log x ^ 2)

def QuadraticSymbolMeanSquare : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (m₀ a₀ : ℕ) (X : ℝ) (κ : ℕ → ℂ),
    0 < m₀ → 8 ∣ m₀ → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (eps / 5) ∨ zz x < p) → a₀.Coprime m₀ → a₀ % 4 = 3 →
    0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X → (∀ n, ‖κ n‖ ≤ 1) →
    X ^ ((9 : ℝ) / 10) ≤ ((PP m₀ a₀ X).card : ℝ) ∧
      (∑ q ∈ PP m₀ a₀ X, ‖Ssum x κ q‖ ^ 2) / (PP m₀ a₀ X).card ≤ 36 * x * Real.log x

def QuadraticSymbolMeanSquareWeak : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (m₀ a₀ : ℕ) (X : ℝ) (κ : ℕ → ℂ),
    0 < m₀ → 8 ∣ m₀ → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (eps / 5) ∨ zz x < p) → a₀.Coprime m₀ → a₀ % 4 = 3 →
    0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X → (∀ n, ‖κ n‖ ≤ 1) →
    κ 1 = 1 → (∀ m n, κ (m * n) = κ m * κ n) →
    X ^ ((9 : ℝ) / 10) ≤ ((PP m₀ a₀ X).card : ℝ) ∧
      (∑ q ∈ PP m₀ a₀ X, ‖Ssum x κ q‖ ^ 2) / (PP m₀ a₀ X).card ≤ C * x * Real.log x

def ChoiceOfFirstModulus : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ q : ℕ, QNum x eps q ∧
    (∀ M : ℕ, M ≠ 0 → 8 * q ∣ M → BoxQ x eps q M) ∧ ‖Ssum x (fun _ => 1) q‖ ≤ x ^ ((1 : ℝ) / 2 + eps) / 2

def ChoiceOfDiscriminant : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, QNum x eps q → ∃ d : ℕ, DNum x eps q d ∧
    BoxD x eps q d (8 * q * d) ∧ ‖Ssum x (fun _ => 1) d‖ ≤ x ^ ((1 : ℝ) / 2 + eps) / 2 ∧
    ‖Ssum x (psDir q) d‖ ≤ x ^ ((1 : ℝ) / 2 + eps) / 2

def ChoiceOfModulusAndDiscriminant : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ q d : ℕ, QNum x eps q ∧ DNum x eps q d ∧
    BoxQ x eps q (8 * q * d) ∧ BoxD x eps q d (8 * q * d) ∧
    BoundsAtX x eps 4 (psDir q) (8 * q * d) ∧ BoundsAtX x eps 4 (chDir d) (8 * q * d) ∧
    BoundsAtX x eps 4 (fun a => chDir d a * psDir q a) (8 * q * d) ∧ kronSym (-(q : ℤ)) d = -1 ∧
    ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x ^ 3 → Real.log (4 * n * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

def UniformZeroFreeRegion : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (x eps : ℝ) (e q d : ℕ), QNum x eps q → DNum x eps q d → BoxQ x eps q (8 * q * d) →
    BoxD x eps q d (8 * q * d) → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharE (2 ^ e) q d χ →
      N ∣ 4 * 2 ^ e * q * d ∧
      ∀ ρ ∈ ntZeros χ, ρ.re ≤ 1 - c / Real.log (((4 * 2 ^ e * q * d : ℕ) : ℝ) * (|ρ.im| + 3))

def ThinScalesBound : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ e q d : ℕ, QNum x eps q → DNum x eps q d →
    BoxQ x eps q (8 * q * d) → BoxD x eps q d (8 * q * d) →
    Real.log (4 * 2 ^ e * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharE (2 ^ e) q d χ →
      ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖gChi χ y‖ ≤ y * Real.exp (-(1 / 2 * x ^ (eps / 8)))

def TypePrimesInDyadicInterval : Prop :=
  ∀ eps A : ℝ, 0 < eps → eps < 1 / 52 → 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (d N r : ℕ) (Y : ℝ),
    d.Prime → d % 4 = 3 → 100 ≤ d → 0 < N → d ∣ N → Real.log N ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 →
    1 ≤ r → (r : ℝ) ≤ x ^ A → Real.exp (x ^ eps) ^ 8 ≤ Y →
    Y ^ ((9 : ℝ) / 10) ≤ (({g : ℕ | g.Prime ∧ Y < g ∧ (g : ℝ) ≤ 2 * Y ∧ NormOne d N g}.ncard : ℕ) : ℝ) ∧
    ∀ E₁ E₂ : Finset ℕ, (E₁.card : ℝ) ≤ Y ^ ((4 : ℝ) / 5) → (E₂.card : ℝ) ≤ Y ^ ((4 : ℝ) / 5) →
      ∃ g₁ g₂ : ℕ, g₁ ∉ E₁ ∧ g₂ ∉ E₂ ∧ g₁ ≠ g₂ ∧ (∀ g ∈ ({g₁, g₂} : Finset ℕ), g.Prime ∧ Y < g ∧ (g : ℝ) ≤ 2 * Y ∧
        NormOne d N g) ∧ Disjoint (Formalism.CyclotomicNorms.BB r g₁) (Formalism.CyclotomicNorms.BB r g₂)

def FewOverlappingExceptionalPrimes : Prop :=
  ∀ (g₁ r : ℕ) (Y : ℝ), g₁.Prime → 1 ≤ r → 1 ≤ Y →
    (({g : ℕ | g.Prime ∧ Y < g ∧ (g : ℝ) ≤ 2 * Y ∧ ¬ Disjoint (Formalism.CyclotomicNorms.BB r g₁) (Formalism.CyclotomicNorms.BB r g)}.ncard : ℕ) : ℝ) ≤
      (3 * r + 1) * (4 * (r : ℝ) ^ 2 * Y ^ ((3 : ℝ) / 4) + 1)

def LevelPrimeShortInterval : Prop :=
  ∀ eps A CY cs : ℝ, 0 < eps → eps < 1 / 52 → 0 < A → 0 < CY → 0 < cs → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (d N g₁ g₂ : ℕ) (Y m F Ts : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 0 < N → d ∣ N →
      Real.log N ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 → 1 ≤ g₁ → 1 ≤ g₂ → (g₁ : ℝ) ≤ 2 * Y → (g₂ : ℝ) ≤ 2 * Y →
      Real.log Y ≤ CY * x ^ eps → x ^ ((1 : ℝ) / 3) ≤ m → 1 ≤ F → F ≤ x ^ A → 0 < Ts → cs * m * x ^ eps ≤ Real.log Ts →
      ∃ T : ℕ, T.Prime ∧ Ts < T ∧ (T : ℝ) ≤ Ts * (1 + 1 / F) ∧ NormOne d (N * (g₁ * g₂) ^ 2) T

def AuxiliaryNormPrimes : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ C' N₀ : ℝ, 0 < C' ∧ ∀ (d N M₀ J : ℕ) (EX : Finset ℕ), d.Prime → d % 4 = 3 → 100 ≤ d → d ∣ N →
    N₀ ≤ N → 0 < N → 1 ≤ M₀ → (M₀ : ℝ) ≤ (N : ℝ) ^ C → (J : ℝ) ≤ (N : ℝ) ^ C → (EX.card : ℝ) ≤ (N : ℝ) ^ C →
    ∃ S : Finset ℕ, S.card = J ∧ ∀ p ∈ S, p.Prime ∧ p ∉ EX ∧ NormOne d (M₀ * N) p ∧ p ≡ 1 [MOD M₀ * N] ∧
      (p : ℝ) ≤ (N : ℝ) ^ C'

end GlobalTheory.NT

end
