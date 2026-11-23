import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtFnOfOfNotMem
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem GlobalTheory.PairStep.discrep_sub_le_zero_of_isQCart : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ)
    (Δ D : X → ℚ) (η : RatForms p n) (x : X) (m mD : ℕ) (gG fD : X.functionFieldˣ) (δ : ℚ),
    IsEffQDiv Δ → IsQCart D → δ ≤ 1 → 0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) →
    ∀ E : DivOver p, (placeEquiv p E).IsPrimeOf (locRing x) → discrep E η m gG - (1 - δ) * (E.ord fD / mD) ≤ 0 := by
  intro X _ _ _ p n Δ D η x m mD gG fD δ hΔ hD hδ hm hmD hlog hDz E hE
  obtain ⟨z, hzx, hEz⟩ := (isPrimeOf_placeEquiv E x).1 hE
  rw [hlog.discrep_eq_neg hm hzx hEz, ← hDz z hzx E hEz]
  have h1 : 0 ≤ Δ z := hΔ.nonneg z
  have h2 : 0 ≤ D z := by
    obtain ⟨m₀, D₀, -, hD₀, rfl⟩ := hD
    refine div_nonneg (Int.cast_nonneg ?_) (Nat.cast_nonneg m₀)
    obtain ⟨g, hg⟩ := D₀.exists_isEqn z
    obtain ⟨a, ha⟩ := CartierDiv.eff_iff.1 hD₀ z g hg
    by_cases hz : Order.coheight z = 1
    · rw [hg.mult_eq, ← ha, ord_algebraMap hz fun h => g.ne_zero (by rw [← ha, h, map_zero])]
      exact Int.natCast_nonneg _
    · rw [hg.mult_eq, Scheme.ord_eq_zero_of_coheight_neq_one hz]
  have h3 : 0 ≤ 1 - δ := by linarith
  nlinarith [mul_nonneg h3 h2]
