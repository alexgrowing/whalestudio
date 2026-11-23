import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegAsm.WeightInf

theorem invVol_nn {G : Type} [Group G] (A B : Subgroup G) : 0 ≤ GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  positivity

theorem invVol_pos' {G : Type} [Group G] (A B : Subgroup G) (h1 : A.relIndex B ≠ 0) (h2 : B.relIndex A ≠ 0) :
    0 < GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  have h1' := Nat.pos_of_ne_zero h1
  have h2' := Nat.pos_of_ne_zero h2
  positivity

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), (∀ (N : NF H r) (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → 0 < N.om Λ ∧ ∀ s ∈ N.R, N.om (s • Λ) = N.om Λ) ∧ ∀ (F F' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V), 0 ≤ omI F F' 𝔡 Λ ∧ (∀ N : NF H r, Adapt F F' 𝔡 N → omI F F' 𝔡 Λ ≤ N.om Λ) ∧ ∀ a c : ℝ, 0 ≤ c → (∃ N : NF H r, Adapt F F' 𝔡 N) → (∀ N : NF H r, Adapt F F' 𝔡 N → a ≤ c * N.om Λ) → a ≤ c * omI F F' 𝔡 Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r
  refine ⟨?_, ?_⟩
  · intro N g Λ hg hT
    have hnil := (GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N).2.2.2.2
    have href := (GlobalTheory.DegCnt.InnerLat.main K V H hK r N g Λ hg hT).2.2.2.2.1
    have hΛ : Submodule.IsLattice K Λ := ((isUnimod_iff H Λ).1 hT.1.1).1
    have h1 := GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil Λ _ hΛ href
    have h2 := GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ Λ href hΛ
    refine ⟨invVol_pos' _ _ h2.1 h1.1, fun s hs => ?_⟩
    have h3 := (GlobalTheory.DegCnt.StabInv.main K V H hK r N g Λ hg hT s hs).2.1.1
    unfold NF.om
    rw [h3]
    exact h1.2 s hs
  · intro F F' 𝔡 Λ
    have hnn : ∀ x ∈ ((fun N : NF H r => N.om Λ) '' {N | Adapt F F' 𝔡 N}), (0 : ℝ) ≤ x := by
      rintro _ ⟨N, -, rfl⟩
      exact invVol_nn _ _
    refine ⟨Real.sInf_nonneg hnn, fun N hN => csInf_le ⟨0, hnn⟩ ⟨N, hN, rfl⟩, ?_⟩
    rintro a c hc ⟨N₀, hN₀⟩ h
    rcases hc.eq_or_lt with rfl | hc
    · simpa using h N₀ hN₀
    · rw [← div_le_iff₀' hc]
      refine le_csInf ⟨_, N₀, hN₀, rfl⟩ ?_
      rintro _ ⟨N, hN, rfl⟩
      rw [div_le_iff₀' hc]
      exact h N hN

end GlobalTheory.DegAsm.WeightInf
