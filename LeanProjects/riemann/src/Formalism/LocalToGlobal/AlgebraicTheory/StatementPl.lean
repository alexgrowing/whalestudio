import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AlgTh

open Formalism.L2.Col (Fields Sp HomE homAt divLat)
open Formalism.L2.Ker (Amb DVar)

def PlaceIota : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (σ₀ : K →+* ℂ) (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 K)),
    0 < Formalism.DivisionValues.vw w (p : K) →
    ∃ ι : ℂ ≃+* ℂ_[p], ∀ x : K, x ≠ 0 →
      ‖ι (σ₀ x)‖ = (p : ℝ) ^ (-(Formalism.DivisionValues.vw w x : ℝ) / (Formalism.DivisionValues.vw w (p : K) : ℝ))

def JetAtW : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime],
    p ≠ 2 → ¬ p ∣ A.d → (∀ ι : ℂ ≃+* ℂ_[p], KerStd A N N' a₀ b₀ c₀ ha hd lam hlam p ι) →
    Formalism.L2.Col.IsSdLat N → Formalism.L2.Col.IsSdLat N' → A.LaHyp a b S →
  ∀ (π : ℂ) (pE : 𝓞 X.E) (pbK : X.K), IsQInt A.d π → π * conj π = (p : ℂ) → SplitS A S p π pE → A.σ₀ pbK = conj π →
  ∀ (c' : ℕ) (x : HomE X.E a b), 0 < c' → ¬ p ∣ c' → x ∈ divLat c' (homAt S N N') →
  ∀ (m : DVar X.Tau a b →₀ ℕ) (w : HeightOneSpectrum (𝓞 X.K)), 0 < Formalism.DivisionValues.vw w (p : X.K) →
    A.jetK S N N' (p * c') x m = 0 ∨
      -((m.degree : ℤ) * Formalism.DivisionValues.vw w pbK) - ((Fintype.card X.Tau * b * a : ℕ) : ℤ) * Formalism.DivisionValues.vw w (p : X.K)
        ≤ Formalism.DivisionValues.vw w (A.jetK S N N' (p * c') x m)

end Formalism.L2.AlgTh
