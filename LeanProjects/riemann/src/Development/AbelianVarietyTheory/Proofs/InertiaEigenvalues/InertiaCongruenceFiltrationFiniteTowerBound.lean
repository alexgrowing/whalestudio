import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoublingArithStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildJumpSumLeOfDetectingCoboundaryCharactersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutatorMemOfCoboundaryDetectsQuotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumOfElementaryAbelianStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumLeAddStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumPowGrowthStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBotStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem finiteTowerBound : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E T : ℕ) (G : ℕ → Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Antitone G → G 0 ≤ lowerRamificationGroup K L 0 → ¬ G 0 ≤ G 1 → (∀ σ ∈ G 0, σ ^ p ∈ G 1) → (∀ j, j + 1 ≤ 2 * T + 8 → ∀ σ ∈ G 0, σ ^ p ∈ G (j + 1) → σ ∈ G j) → (∀ k ≤ 2 * T, Detects p 8 (G k) (G (k + 8))) → 2 ^ T * Nat.card ↥(G 0) < E := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E T G hp hE hord hax hanti h0 h01 hpow hlift hdet

  have hG0 : ∀ k, G k ≤ lowerRamificationGroup K L 0 := fun k => le_trans (hanti (Nat.zero_le k)) h0

  have hcomm : ∀ k ≤ 2 * T, ∀ σ ∈ G k, ∀ τ ∈ G k, σ * τ * σ⁻¹ * τ⁻¹ ∈ G (k + 8) :=
    fun k hk => GlobalTheory.T.commutator_mem_of_coboundary_detects_quotient K L p E 8 (G k) (G (k + 8)) hp hE hord (hdet k hk)
  obtain ⟨hw, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot K L

  refine doublingArith (fun a b => jumpSum (wild K L) (G a) (G b)) E T (Nat.card ↥(G 0)) hE ?_ ?_ ?_ ?_
  · intro k hk j hj1 hj8
    refine GlobalTheory.T.ramificationJumpSum_pow_growth K L p E (G k) (G (k + j)) (G (k + j + 1)) (hG0 k) hord ?_ ?_
    · intro σ hσ τ hτ
      exact hanti (show k + j + 1 ≤ k + 8 by omega) (hcomm k hk σ hσ τ hτ)
    · intro σ hσ hσp
      exact hlift (k + j) (by omega) σ (hanti (Nat.zero_le k) hσ) hσp
  · intro k hk
    exact GlobalTheory.T.wildJumpSum_le_of_detecting_coboundary_characters K L p E 8 (G k) (G (k + 8)) hp hE hord hax (hdet k hk)
  · intro k
    exact GlobalTheory.T.ramificationJumpSum_le_add _ (wild K L) (G k) (G (k + 2)) (G (k + 3)) hw hbot (hanti (Nat.le_add_right k 2))
  · refine GlobalTheory.T.card_le_wildJumpSum_of_elementaryAbelian K L p E (G 0) (G 1) hp hE h0 hord ?_ hpow h01
    intro σ hσ τ hτ
    exact hanti (show 1 ≤ 0 + 8 by omega) (hcomm 0 (Nat.zero_le _) σ hσ τ hτ)

end GlobalTheory.PMon.Ram
