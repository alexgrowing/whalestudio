import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.HolomorphicIntegrality.HolInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRingOfIntegersOfHol
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerNeZero

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.KU.sgU :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ), GlobalTheory.Sieg.admitted c x → IsU X (siegel X c x) := by
  intro Ω _ _ _ ε X c x hx
  have hne := siegel_ne_zero Ω ε X c x hx
  obtain ⟨h1, h2⟩ := TopUnits.siegel_hol X hx
  refine ⟨hne, fun W hW => ?_⟩
  have a1 := (W.valuation_le_one_iff _).mpr (KU.hol Ω ε X _ h1 W hW)
  have a2 := (W.valuation_le_one_iff _).mpr (KU.hol Ω ε X _ h2 W hW)
  have a3 : W.valuation (siegel X c x) * W.valuation (siegel X c x)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hne, map_one]
  refine le_antisymm a1 ?_
  by_contra hlt
  push_neg at hlt
  have := mul_lt_one_of_lt_of_le hlt a2
  rw [a3] at this
  exact lt_irrefl _ this
