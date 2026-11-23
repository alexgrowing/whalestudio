import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAddValuationFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.UnramifiedChar

theorem norm_eq_one_of_compact {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField k]
    (d : Γ →* k) (hd : Continuous d) (g : Γ) : ‖d g‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_norm.comp hd)).bddAbove
  have hle : ∀ g, ‖d g‖ ≤ 1 := by
    intro g
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    have : ‖d (g ^ n)‖ ≤ C := hC ⟨g ^ n, rfl⟩
    rw [map_pow, norm_pow] at this
    linarith
  have h1 : ‖d g‖ * ‖d g⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, mul_inv_cancel, map_one, norm_one]
  have := hle g; have := hle g⁻¹; have := norm_nonneg (d g); have := norm_nonneg (d g⁻¹)
  nlinarith

variable {l : ℕ} [Fact l.Prime]

theorem val_mem_OL (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ)
    (hμ : Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) (g : ↥(GK K)) :
    ((μ g : (↥LL.1)ˣ) : ↥LL.1) ∈ OL LL := by
  haveI := GlobalTheory.UnramifiedCrys.compactSpace_GK K
  let d : ↥(GK K) →* Om l :=
    ((LL.1.val : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →* Om l).comp ((Units.coeHom ↥LL.1).comp μ)
  have hd : Continuous d := continuous_subtype_val.comp hμ
  exact (GlobalTheory.Per.Val.mem_OL_iff LL _).2 (norm_eq_one_of_compact d hd g).le

def unitLat (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ)
    (hμ : Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := ↥LL.1
  ρ := charRep μ
  cont := fun x => hμ.mul continuous_const
  L := GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.charLat Subtype.val_injective μ fun g => ⟨⟨_, val_mem_OL K LL μ hμ g⟩, rfl⟩

theorem isCrys_and_multV_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ), Continuous (fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g ∈ IK K, μ g = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = 0 then 1 else 0 := by
  intro l _ P AI T K LL μ hμ hI
  obtain ⟨hc, hj⟩ := GlobalTheory.UnramifiedRep.isCrys_and_jump_eq_zero l P AI T K LL (unitLat K LL μ hμ)
    (fun g hg (x : ↥LL.1) => by
      change ((μ g : (↥LL.1)ˣ) : ↥LL.1) * x = x
      rw [hI g hg, Units.val_one, one_mul])
  change IsCrys (P.PD K) (charRep μ) at hc
  change ∀ τ a, IsJumpV (P.PD K) (charRep μ) τ a → a = 0 at hj
  refine ⟨hc, fun τ b => ?_⟩
  obtain ⟨hcomp, -⟩ := GlobalTheory.Per.Components.components_finrank l P AI T K LL ↥LL.1 (charRep μ)
  obtain ⟨hfd, -, hdr⟩ := hcomp τ
  haveI := hfd
  have hdim : finrank ↥LL.1 ↥(DdRE (P.PD K) (charRep μ) τ) = 1 := by
    rw [hdr (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL ↥LL.1 (charRep μ) hc).1, finrank_self]
  have hnj : ∀ a, a ≠ 0 → multV (P.PD K) (charRep μ) τ a = 0 := fun a ha =>
    Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_of_not_jump (P.PD K) (charRep μ) τ a (fun h => ha (hj τ a h))
  split_ifs with hb
  · subst hb
    obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) (charRep μ) τ
    obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) (charRep μ) τ
    have hsum := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV (P.PD K) (charRep μ) τ (min lo 0) (max hi 1) (by omega)
    rw [hlo _ (min_le_left _ _), hhi _ (le_max_left _ _), finrank_bot, Nat.cast_zero, sub_zero, hdim,
      Finset.sum_eq_single (0 : ℤ) (fun a _ ha => hnj a ha)
        (fun h => absurd (Finset.mem_Ico.2 ⟨min_le_right _ _, by omega⟩) h)] at hsum
    exact_mod_cast hsum
  · exact hnj b hb

end GlobalTheory.UnramifiedChar
