import Formalism.PeriodIntegrals.NablaSpans.MinorProdSpanHasCompl

noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW

abbrev nablaSpanC (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 : ℕ)
    (nu : Lt → YoungDiagram) : Submodule ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]) :=
  Submodule.span ℂ_[l] (Set.range fun J : ColChoice N0 nu =>
    MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J))

def StepBack : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (B : ℝ),
    ExpansionCoeffValuationGe N0 N1 l nu Th B → KvalGe N0 N1 l nu Th B

def StepSpan : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (I : ColChoice N1 nu),
    applyAt0 N0 N1 l Th (Gxz N0 N1 nu I) ∈ nablaSpanC Lt l N0 nu

def StepSat : Prop :=
  MinorProdSpanHasCompl → ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 : ℕ)
    (nu : Lt → YoungDiagram) (P : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]) (B : ℝ),
    P ∈ nablaSpanC Lt l N0 nu →
    (∀ m, ‖MvPolynomial.coeff m P‖ ≤ (l : ℝ) ^ (-B)) →
    ∃ c : ColChoice N0 nu →₀ ℂ_[l], (∀ J, ‖c J‖ ≤ (l : ℝ) ^ (-B)) ∧
      P = c.sum fun J a => a • MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)

end GenFrameSpan
