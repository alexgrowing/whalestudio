import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Statement

theorem UpperTheory.Reformulated.B.Rb6.norm_le_one_of_mem :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l)
    {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ c.O →
      ‖x‖ ≤
        (1 :
          ℝ) := by
  intro l _ c x hx
  have h1 : IsIntegral ℤ_[l] (⟨x, hx⟩ : c.O) := Algebra.IsIntegral.isIntegral _
  have h2 : IsIntegral ℤ_[l] x := h1.map c.O.val
  have h3 : IsIntegral ℚ_[l] x := h2.tower_top
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic h3),
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h2]
  intro n
  rw [Polynomial.coeff_map]
  exact PadicInt.norm_le_one _
