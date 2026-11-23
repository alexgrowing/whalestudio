import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankZetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenUnitMinorSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankEqOfUnitMinorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGroupOfUnitMinorStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMinorStableIntegralGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankNormalFormOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenCoverFiniteTranslatesSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenIntegrabilityFullRankOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOrbitalIntegralStableStatement

noncomputable section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv

theorem mem_augRk_of_fibre_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ h : GL (Fin d) k, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = 0) →
      Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  intro k _ _ _ _ _ _ n d ν hnd hν Ψ hΨ hT
  have hT' : ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n →
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y = 0 := fun Y hY => by
    obtain ⟨h, rfl⟩ := GlobalTheory.T.full_rank_normal_form_orbit k n d hnd Y hY
    exact hT h
  obtain ⟨s, hs⟩ := GlobalTheory.T.open_cover_finite_translates_support k n d _ (GlobalTheory.T.isClopen_unit_minor_set k n d).isOpen (GlobalTheory.T.exists_unit_minor_translate k n d) Ψ hΨ
  obtain ⟨Φ, hΦ, hS, hdiff, hF⟩ := GlobalTheory.T.clopen_integrability_full_rank_orbit k n d ν _ (GlobalTheory.T.isClopen_unit_minor_set k n d)
    (fun Φ hΦ Y => GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Φ hΦ Y) s Ψ hΨ hs
  have hA := GlobalTheory.T.smooth_character_orbital_integral_stable k n d ν hν _ (GlobalTheory.T.integral_group_of_unit_minor_stable k n d) (fun E hE Y hY => GlobalTheory.T.unit_minor_stable_integral_group k n d E Y hE hY) Φ hΦ hS
    (fun Y hY => by rw [hF]; exact hT' Y (GlobalTheory.T.rank_eq_of_unit_minor k n d Y hY))
  have e : Ψ = (Ψ - Φ) + Φ := by abel
  rw [e]; exact add_mem hdiff hA

end GlobalTheory.FullRankCoinv
