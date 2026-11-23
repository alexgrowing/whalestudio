import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulHerbrandPhiNatCastTotallyRamifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBotStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_mul_le_jumpSum_of_mem_upper_not_mem : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)) (v : ℝ),
    lowerRamificationGroup F L 0 = ⊤ → ∀ σ ∈ upperRamificationGroup F L v, σ ∉ B →
      (Nat.card (L ≃ₐ[F] L) : ℝ) * v ≤ (jumpSum (wild F L) ⊤ B : ℝ) := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ B v h0 σ hσ hσB
  have hσ1 : σ ≠ 1 := fun h ↦ hσB (h ▸ B.one_mem)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top (K := F) (L := L) hσ1)
  have hm1 : 1 ≤ m := by
    have : (1 : ℕ∞) ≤ lowerIndex F L σ := one_le_lowerIndex_iff.mpr (h0 ▸ Subgroup.mem_top σ)
    rw [← hm] at this
    exact_mod_cast this
  have hv := (mem_upperRamificationGroup_iff_of_lowerIndex_eq hm.symm).mp hσ
  have hcast : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm1]; simp
  rw [hcast] at hv
  obtain ⟨hanti, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot F L
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_initialSegment_not_inf_le_filtration (L ≃ₐ[F] L) (wild F L) ⊤ B hanti hbot
  have hjs := GlobalTheory.T.ramificationJumpSum_eq_sum_range (L ≃ₐ[F] L) (wild F L) ⊤ B n hanti hn
  have hphi := GlobalTheory.T.card_mul_herbrandPhi_natCast_totallyRamified F L h0 (m - 1)
  have hle : m - 1 ≤ n := by
    by_contra hlt
    push_neg at hlt
    have hmem : σ ∈ wild F L n := by
      rw [wild, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hm]
      exact_mod_cast (by omega : n + 1 + 1 ≤ m)
    have : ¬ (⊤ ⊓ wild F L n ≤ B) := fun h ↦ hσB (h ⟨Subgroup.mem_top σ, hmem⟩)
    exact lt_irrefl n ((hn n).mpr this)
  have hcard : (0 : ℝ) ≤ (Nat.card (L ≃ₐ[F] L) : ℝ) := Nat.cast_nonneg _
  calc (Nat.card (L ≃ₐ[F] L) : ℝ) * v ≤ (Nat.card (L ≃ₐ[F] L) : ℝ) * herbrandPhi F L ((m - 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hv hcard
    _ = ((∑ t ∈ Finset.range (m - 1), Nat.card ↥(wild F L t) : ℕ) : ℝ) := hphi
    _ ≤ (jumpSum (wild F L) ⊤ B : ℝ) := by
        rw [hjs]
        simp only [top_inf_eq]
        exact_mod_cast Finset.sum_le_sum_of_subset ((Finset.range_subset_range.mpr hle))

end GlobalTheory.PMon.Ram
