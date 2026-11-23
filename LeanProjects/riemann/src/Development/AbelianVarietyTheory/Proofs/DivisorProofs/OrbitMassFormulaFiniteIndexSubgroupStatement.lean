import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitMassFormulaFiniteIndexSubgroup
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_mass_formula_finiteIndex_subgroup : ∀ {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D] (ι : H →* G), Function.Injective ι → (∀ (h : H) (d : D), ι h • d = h • d) → ι.range.FiniteIndex → (∀ d : D, Finite (MulAction.stabilizer G d)) → ∀ [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient H D)] (f : D → ℂ), (∀ (g : G) (d : D), f (g • d) = f d) → ∑ c : MulAction.orbitRel.Quotient H D, ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) = (ι.range.index : ℂ) * ∑ c : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) := by
  first | exact @GlobalTheory.OrbitMass.mass_formula | exact GlobalTheory.OrbitMass.mass_formula | (intros; apply GlobalTheory.OrbitMass.mass_formula <;> assumption)
