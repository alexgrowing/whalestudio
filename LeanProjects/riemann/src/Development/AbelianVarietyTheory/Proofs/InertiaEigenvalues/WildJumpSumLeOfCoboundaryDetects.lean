import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpSumKernelCoboundaryCharLeSixMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumMonoOfLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBotStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_wild_top_le_of_detects : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → Detects p r ⊤ B → jumpSum (wild F L) ⊤ B ≤ 6 * E := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E r B hp hE hord hax hdet
  obtain ⟨hanti, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot F L
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_initialSegment_not_inf_le_filtration _ (wild F L) ⊤ B hanti hbot
  rcases n with _ | k
  · rw [GlobalTheory.T.ramificationJumpSum_eq_sum_range _ (wild F L) ⊤ B 0 hanti hn]
    simp
  · have hk : ¬ (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L k ≤ B := (hn k).1 (Nat.lt_succ_self k)
    obtain ⟨σ₀, hσ₀, hσ₀B⟩ := SetLike.not_le_iff_exists.1 hk
    have hσ₀k : σ₀ ∈ wild F L k := (Subgroup.mem_inf.1 hσ₀).2
    obtain ⟨x, a, hxa, hnd⟩ := hdet σ₀ (Subgroup.mem_top σ₀) hσ₀B
    obtain ⟨J, hJ, hJsum⟩ := GlobalTheory.T.jumpSum_kernel_coboundaryChar_le_six_mul F L p E r x a hp hE hord hax
      (fun σ => hxa σ (Subgroup.mem_top σ)) ⟨σ₀, hnd⟩
    have hσ₀J : σ₀ ∉ J := fun h => hnd ((hJ σ₀).1 h)
    have hmono : ∀ t, (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L t ≤ J → (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L t ≤ B := by
      intro t ht
      by_contra hB
      have htk : t ≤ k := Nat.lt_succ_iff.1 ((hn t).2 hB)
      have hσ₀t : σ₀ ∈ wild F L t := hanti htk hσ₀k
      exact hσ₀J (ht (Subgroup.mem_inf.2 ⟨Subgroup.mem_top σ₀, hσ₀t⟩))
    exact le_trans (GlobalTheory.T.ramificationJumpSum_mono_of_le _ (wild F L) ⊤ B J hanti hbot hmono) hJsum

end GlobalTheory.PMon.Ram
