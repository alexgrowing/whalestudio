import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsBottomOfIsCoprime

open GlobalTheory.SqTop Formalism.BasicNotions

namespace GlobalTheory.SqTop

theorem botEx_holds (_ : ∀ D, GlobalTheory.NormSum.Inp D) : BotEx := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
  obtain ⟨δ, t0, h⟩ := GlobalTheory.FunObj.SqNum.exists_isBottom hL G ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩
  exact ⟨δ, t0, fun ij => h ij.1 ij.2⟩

end GlobalTheory.SqTop
