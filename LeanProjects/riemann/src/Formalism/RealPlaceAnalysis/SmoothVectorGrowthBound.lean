import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
import Formalism.RealPlaceAnalysis.SmoothOnG
import Formalism.RealPlaceAnalysis.StatementA

open MeasureTheory

noncomputable section

namespace Formalism.REAL

def hh {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.log (hs g)

def Eword {n : ℕ} (ε : Fin n → Bool) : List (Fin n × Fin n) →
    (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ)
  | [] => id
  | p :: w => fun f => Eab ε p.1 p.2 (Eword ε w f)

def CasF {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a, ∑ b, Eab ε a b (Eab ε b a f) g

abbrev toM {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

def HhLip : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    SmoothOnG ε (fun x => ((hh x : ℝ) : ℂ)) ∧
    ∀ (X g : Matrix (Fin n) (Fin n) ℂ), inG ε X → inUJ ε g →
      ‖Rd X (fun x => ((hh x : ℝ) : ℂ)) g‖ ≤ 2 * Real.sqrt (hs X)

def IntRdZero : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (R : ℝ), SmoothOnG ε φ → inG ε X → (∀ g, inUJ ε g → R < hs g → φ g = 0) →
    ∫ g : UJ ε, Rd X φ (toM g) ∂(muG ε) = 0

def SmoothVectorGrowthBound : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) (c : ℂ) (a : ℝ),
    FiniteDimensional ℂ W → 0 ≤ a →
    (∀ w ∈ W, SmoothOnG ε w) →
    (∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, inUJ ε g → Eab ε i j w g = w' g) →
    (∀ w ∈ W, ∀ g, inUJ ε g → CasF ε w g = c * w g) →
    (∀ w ∈ W, Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖w (toM g)‖ ^ 2) (muG ε)) →
    ∀ (w₁ w₂ : List (Fin n × Fin n)) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ), f ∈ W → f' ∈ W →
      SmoothOnG ε (Eword ε w₁ f) ∧
      Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eword ε w₁ f (toM g)‖ ^ 2) (muG ε) ∧
      ∀ i j : Fin n,
        ∫ g : UJ ε, Eab ε i j (Eword ε w₁ f) (toM g) * starRingEnd ℂ (Eword ε w₂ f' (toM g)) ∂(muG ε) =
          (sgn ε i j : ℂ) *
            ∫ g : UJ ε, Eword ε w₁ f (toM g) * starRingEnd ℂ (Eab ε j i (Eword ε w₂ f') (toM g)) ∂(muG ε)

end Formalism.REAL
