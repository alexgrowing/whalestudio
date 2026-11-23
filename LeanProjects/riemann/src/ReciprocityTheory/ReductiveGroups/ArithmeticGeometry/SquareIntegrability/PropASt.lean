import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

def GT.Coc {ι : Type} [Fintype ι] (Y : GT ι) (q : ℕ) : Prop :=
  ∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
    Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I)

open Classical in

def PropAStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Y : GT ι) (q c : ℕ) (R0 : ℝ), 1 ≤ q → Y.Coc q → 0 < R0 →
    (∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖) →
    270 ≤ R0 ^ 2 → 90 * ((Fintype.card ι : ℝ) + c) ≤ R0 ^ 2 →
    ∀ p : MvPolynomial ι ℂ, p.totalDegree ≤ c →
      ∃ β ∈ Y.Sec q,
        (∀ α : ι →₀ ℕ, α.degree ≤ c →
          polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) β 0 =
            polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1)
              (fun v : EuclideanSpace ℂ ι => MvPolynomial.eval (fun i => v i) p) 0) ∧
        Y.l2 q β ≤ 6 * ∫ v : EuclideanSpace ℂ ι, ‖MvPolynomial.eval (fun i => v i) p‖ ^ 2 *
          Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)

end

end ReciprocityTheory.ChartRestriction.G.I2
