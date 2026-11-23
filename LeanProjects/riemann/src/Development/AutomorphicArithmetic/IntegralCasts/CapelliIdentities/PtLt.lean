import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Statement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLtOne

theorem UpperTheory.Reformulated.B.Gs4b.pt_lt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {c : UpperTheory.V.HV.Coef l} {R : Type} [inst_1 : CommRing R]
      [inst_2 : Algebra (↥c.O) R] [inst_3 : IsLocalRing R] (y : R →ₐ[↥c.O] Formalism.ConjugateSelfDual.Qbar l),
      ∀ a ∈ IsLocalRing.maximalIdeal R, ‖(y : R → Formalism.ConjugateSelfDual.Qbar l) a‖ < (1 : ℝ) := by
  intro l _ c R _ _ _ y a ha
  exact UpperTheory.Reformulated.B.NormLtOne.norm_lt_one (l := l) (O := ↥c.O) y a ha
