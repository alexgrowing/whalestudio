import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtAddSmulOfLcAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureLeOfSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalLogCanonicalGenerisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogEqnAddSmulIffOfOff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem logCanonicalCut_of_step : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D B : X → ℚ) (δ c : ℚ) (x z : X) (j : ℕ), KltAt p n Δ x → IsQCart D → IsQCart B →
      LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → c ≤ 1 → Off B z →
      (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) →
      topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) →
      LcAt p n (Δ + (1 - δ) • D + c • B) x → ¬ KltAt p n (Δ + (1 - δ) • D + c • B) x →
      LcCut p n (Δ + (1 - δ) • D + c • B) x j := by
  intro X _ _ _ p n hp hn Δ D B δ c x z j hk hD hB hl hδ hδ1 hc hoff hsep hdim hlc hnk
  refine ⟨hlc, hnk, fun w hwx hw => ?_⟩
  have hx : KltAt p n (Δ + (1 - δ) • D) x :=
    kltAt_add_smul_of_lcAt X p n hp hn Δ D δ x hD hk hl hδ hδ1
  have hkw : KltAt p n (Δ + (1 - δ) • D) w :=
    (GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation X p n (Δ + (1 - δ) • D) x w hwx).1 hx
  by_cases hzw : z ⤳ w
  · by_cases hwz : w = z
    · subst hwz
      exact absurd ((off_add_smul X p n (Δ + (1 - δ) • D) B c w hoff).1.2 hkw) hw
    · exact topologicalKrullDim_closure_le_of_specializes X z w j hzw hwz hdim
  · exfalso
    have h1 : KltAt p n (Δ + (1 - δ) • D + (1 : ℚ) • B) w := by
      rw [one_smul]; exact hsep w hzw (1 - δ) (by linarith) hkw
    exact hw ((GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hn (Δ + (1 - δ) • D) B c 1 w hB hc).1 h1)

end GlobalTheory.PairStep

example : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D B : X → ℚ) (δ c : ℚ) (x z : X) (j : ℕ), KltAt p n Δ x → IsQCart D → IsQCart B → LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → c ≤ 1 → Off B z → (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) → topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) → LcAt p n (Δ + (1 - δ) • D + c • B) x → ¬ KltAt p n (Δ + (1 - δ) • D + c • B) x → LcCut p n (Δ + (1 - δ) • D + c • B) x j :=
  GlobalTheory.PairStep.logCanonicalCut_of_step
