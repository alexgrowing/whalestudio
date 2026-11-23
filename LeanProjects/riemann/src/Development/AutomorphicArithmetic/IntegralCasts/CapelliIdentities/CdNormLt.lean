import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLtOne

theorem UpperTheory.Reformulated.B.Gs5b.cd_norm_lt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) {R : Type} [inst_1 : CommRing R] [inst_2 : IsLocalRing R]
      [inst_3 : Algebra (↥c.O) R] (y : R →ₐ[↥c.O] PadicAlgCl l),
      ∀ a ∈ IsLocalRing.maximalIdeal R, ‖(y : R → PadicAlgCl l) a‖ < (1 : ℝ) := by
  intro l _ c R _ _ _ y a ha
  exact UpperTheory.Reformulated.B.NormLtOne.norm_lt_one y a ha
