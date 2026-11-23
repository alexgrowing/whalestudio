import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualAndPrincipalCongruenceOrbitsOfGoodLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_and_principalCongruence_orbits_of_goodLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, GlobalTheory.EqCovol.IsSelfDualTr (U.X k) ∧ ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ γ' : GL (Fin r) E, IsUStab (U.X k).Gm (U.X k).Λ γ' ∧ (∀ v ∈ (U.X k).Λ, ∃ w ∈ (U.X k).Λ, (γ' : Matrix (Fin r) (Fin r) E).mulVec v - v = l.M' • w) ∧ ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b := by
  first | exact @GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf | exact GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf | (intros; apply GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf <;> assumption)
