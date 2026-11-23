import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallPacking
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNmSectionsRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionsSeparated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPacking
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

theorem SmallPacking.proof (hR : NmSectionsRankBound.Statement) (hS : SmallSectionsSeparated.Statement) :
    SmallPacking.Statement := by
  classical
  intro K _ ι _ Ω _ y D A La hX hB hA hLa
  obtain ⟨hfin, C₁, hC₁, hrank⟩ := hR K ι Ω y D A.a hX hB
  obtain ⟨C, hC, hsep⟩ := hS K ι Ω y D A hX hB hA
  have key : ∀ (τ : ℕ) (T : Finset (La τ)), (∀ s ∈ T, IsSmallH (mCoordIdeal y) y A τ (s : Ω)) →
      Real.log T.card ≤ C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3) := by
    intro τ T hT
    obtain ⟨Z, ev, hZ, hrep, hsepτ⟩ := hsep τ
    have hpos : ∀ z : Z, 0 < A.h z := fun z => A.pos _ (hZ z z.2).1
    let φ : chartLatNm y A.a τ →+ (Z → ℂ) :=
      { toFun := fun s z => ev s z / ((A.h z : ℂ) ^ τ)
        map_zero' := by funext z; simp
        map_add' := by intro s t; funext z; simp [add_div] }
    have hφ : ∀ s z, ‖φ s z‖ = ‖ev s z‖ / A.h z ^ τ := fun s z => by
      simp [φ, norm_pow, abs_of_pos (hpos z)]
    have hnorm : ∀ s : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) → ‖φ s‖ ≤ 1 := by
      intro s hs
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun z => ?_
      obtain ⟨dg, dh, g, h, hg, hh, hdeg, heq, hz0, hev⟩ := hrep s z
      have hle := hs dg dh g h z hg hh hdeg heq (hZ z z.2)
      rw [← hev, norm_mul] at hle
      rw [hφ, div_le_one (pow_pos (hpos z) τ)]
      exact le_of_mul_le_mul_right (by linarith) (norm_pos_iff.2 hz0)
    have hdist : ∀ s t : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) →
        IsSmallH (mCoordIdeal y) y A τ (t : Ω) → s ≠ t →
        Real.exp (-(C * ((τ : ℝ) + 1))) ≤ ‖φ s - φ t‖ := by
      intro s t hs ht hst
      obtain ⟨z, hz⟩ := hsepτ s t hs ht hst
      refine le_trans ?_ (norm_le_pi_norm (φ s - φ t) z)
      rw [← map_sub φ, hφ, map_sub ev, Pi.sub_apply, le_div_iff₀ (pow_pos (hpos z) τ)]
      exact hz
    let ι' : La τ →+ chartLatNm y A.a τ := AddSubgroup.inclusion (hLa τ)
    have := hfin τ
    let L : Submodule ℤ (Z → ℂ) := LinearMap.range φ.toIntLinearMap
    have hsmall : ∀ s ∈ T, IsSmallH (mCoordIdeal y) y A τ ((ι' s : chartLatNm y A.a τ) : Ω) := hT
    have hinj : Set.InjOn (fun s => φ (ι' s)) T := by
      intro s hs t ht hst
      by_contra hne
      have hne' : ι' s ≠ ι' t := fun h => hne (Subtype.ext (by simpa [ι'] using congrArg Subtype.val h))
      have := hdist _ _ (hsmall s hs) (hsmall t ht) hne'
      simp only at hst
      rw [hst, sub_self, norm_zero] at this
      exact absurd this (not_le.2 (Real.exp_pos _))
    have hP := Packing.proof (Z → ℂ) L (T.image fun s => φ (ι' s)) (C * ((τ : ℝ) + 1)) (by positivity)
      (by intro v hv; obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hv; exact ⟨ι' s, rfl⟩)
      (by intro v hv; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv; exact hnorm _ (hsmall s hs))
      (by
        intro v hv w hw hvw
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hw
        exact hdist _ _ (hsmall s hs) (hsmall t ht) fun h => hvw (by rw [h]))
    rw [Finset.card_image_of_injOn hinj] at hP
    have hL : (Module.finrank ℤ L : ℝ) ≤ Module.finrank ℤ (chartLatNm y A.a τ) := by
      exact_mod_cast LinearMap.finrank_range_le φ.toIntLinearMap
    refine hP.trans (mul_le_mul_of_nonneg_right (hL.trans (hrank τ)) (by positivity))
  have hfinite : ∀ τ, {s : La τ | IsSmallH (mCoordIdeal y) y A τ (s : Ω)}.Finite := by
    intro τ
    by_contra hinf
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (⌈Real.exp (C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3))⌉₊ + 1)
    have h1 := key τ T (fun s hs => hTsub hs)
    rw [hTcard, Real.log_le_iff_le_exp (by positivity)] at h1
    push_cast at h1
    linarith [Nat.le_ceil (Real.exp (C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3)))]
  refine ⟨hfinite, C₁ * (C + Real.log 3), fun τ => ?_⟩
  unfold smallSectionCount
  rw [show Nat.card {s : La τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} = (hfinite τ).toFinset.card from
    Nat.card_eq_card_finite_toFinset (hfinite τ)]
  refine (key τ _ fun s hs => (hfinite τ).mem_toFinset.1 hs).trans ?_
  have h1 : (1 : ℝ) ≤ (τ : ℝ) + 1 := by linarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ)]
  have hl : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  calc C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3)
      ≤ C₁ * ((τ : ℝ) + 1) ^ D * ((C + Real.log 3) * ((τ : ℝ) + 1)) := by gcongr; nlinarith
    _ = C₁ * (C + Real.log 3) * ((τ : ℝ) + 1) ^ (D + 1) := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
