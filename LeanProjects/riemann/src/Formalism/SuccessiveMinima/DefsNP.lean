import Formalism.SuccessiveMinima.StatementNP

open Filter Topology

noncomputable section

namespace Formalism.FN

def cmul {K : Type*} [NormedField K] (a b : ℕ → K) : ℕ → K :=
  fun n => ∑ i ∈ Finset.range (n + 1), a i * b (n - i)

def GaussMul : Prop :=
  ∀ {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] (a b : ℕ → K) (r : ℝ),
    0 < r → ConvOn a r → ConvOn b r → a ≠ 0 → b ≠ 0 →
      ConvOn (cmul a b) r ∧ gNorm (cmul a b) r = gNorm a r * gNorm b r ∧
        wdeg (cmul a b) r = wdeg a r + wdeg b r

def EvalMul : Prop :=
  ∀ {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (a b : ℕ → K) (r : ℝ), 0 < r → ConvOn a r → ConvOn b r →
      ∀ x : K, ‖x‖ ≤ r → evalS (cmul a b) x = evalS a x * evalS b x

def WDivision : Prop :=
  ∀ {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (f g : ℕ → K) (r : ℝ), 0 < r → ConvOn f r → ConvOn g r → g ≠ 0 →
      ∃ q : ℕ → K, ConvOn q r ∧ ∃ R : Polynomial K, R.degree < (wdeg g r : WithBot ℕ) ∧
        (∀ j : ℕ, ‖R.coeff j‖ * r ^ j ≤ gNorm f r) ∧ ∀ n : ℕ, f n = cmul q g n + R.coeff n

def UnitFacts : Prop :=
  ∀ {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (b : ℕ → K) (r : ℝ), 0 < r → ConvOn b r → b ≠ 0 → wdeg b r = 0 →
      (∀ x : K, ‖x‖ ≤ r → ‖evalS b x‖ = gNorm b r) ∧
      ∃ u : ℕ → K, ConvOn u r ∧ cmul b u = fun n => if n = 0 then 1 else 0

end Formalism.FN
