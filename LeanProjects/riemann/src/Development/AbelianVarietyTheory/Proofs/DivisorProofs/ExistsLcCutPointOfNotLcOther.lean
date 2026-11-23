import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtAddSmulOfLcAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltAtPointsNotContainingCentreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonKltLocusDimLtAfterPerturbationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultNsmulOfQadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectiveQCartierDivisorConvexConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffQCartierNumEquivMultipleNonnegSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotKltAtSubOfNotLcAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalLogCanonicalThresholdAtPointStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_lcCut_of_not_lcAt : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (d h : ℚ) (x x' z : X) (j : ℕ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → QNum p N d D → 0 ≤ d → IsClosed ({x} : Set X) → LcAt p n (Δ + D) x → ¬ LcAt p n (Δ + D) x' → z ⤳ x → IsNkltCentre p n (Δ + D) z → topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) → 0 < h → ((j + 1 : ℕ) : ℚ) ^ (j + 1) < h ^ (j + 1) * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin (j + 1) => N : ℤ) → ∃ (D' : X → ℚ) (d' : ℚ), 0 ≤ d' ∧ d' ≤ d + h ∧ QNum p N d' D' ∧ LcCut p n (Δ + D') x j ∧ ¬ KltAt p n (Δ + D') x' := by
  intro hPr hNad hNef X _ _ _ p n hp hn Δ m G N D d h x x' z j hΔ hklt hm hG hN hQ hd hx hlc hnlc
    hzx hz hzd hh hdeg
  have hDq : IsQCart D := QNum.isQCart hQ

  obtain ⟨B, δ₀, hδ₀, hδ₀1, hBq, hoff, hnk, hfar⟩ :=
    GlobalTheory.T.exists_divisor_nonKlt_at_points_not_containing_centre hPr hNad hNef X p n hp hn Δ m G N D {x} z (j + 1) h hΔ hklt hm hG hN hDq
      (by simp [hx, hzx]) (by omega) hzd (Or.inr hz) hh (by simpa using hdeg)

  obtain ⟨δ₁, hδ₁, hx'⟩ := GlobalTheory.T.exists_not_kltAt_sub_of_not_lcAt X p n hp hn Δ D x' hDq (hklt x') hnlc
  obtain ⟨δ, hδ, hδ1, hδa, hδb⟩ : ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ δ₀ ∧ δ ≤ δ₁ :=
    ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, (min_le_left _ _).trans hδ₀1, min_le_left _ _, min_le_right _ _⟩
  have hBc : IsQCart B := QNum.isQCart hBq
  have hDδ : IsQCart ((1 - δ) • D) := (GlobalTheory.T.isEffectiveQCartierDivisor_convexCone X D D (1 - δ) hDq hDq (by linarith)).2.1

  have hkx : KltAt p n (Δ + (1 - δ) • D) x := GlobalTheory.T.kltAt_add_one_sub_smul_of_kltAt_of_lcAt X p n hp hn Δ D δ x hDq (hklt x) hlc hδ hδ1
  have hnkx : ¬ KltAt p n (Δ + (1 - δ) • D + B) x := hnk δ hδ.le hδa x (Finset.mem_singleton_self x)

  obtain ⟨c, hc, hc1, hlcx, hnklx⟩ :=
    GlobalTheory.T.exists_rational_logCanonicalThreshold_at_point hPr X p n hp hn Δ m G ((1 - δ) • D) B x hm hG hDδ hBc hkx hnkx
  have hcut : LcCut p n (Δ + (1 - δ) • D + c • B) x j :=
    GlobalTheory.T.nonKlt_locus_dim_lt_after_perturbation X p n hp hn Δ D B δ c x z j (hklt x) hDq hBc hlc hδ hδ1 hc1 hoff hfar hzd hlcx hnklx
  refine ⟨(1 - δ) • D + c • B, (1 - δ) * d + c * h, ?_, ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ 1 - δ := by linarith
    positivity
  · nlinarith [mul_nonneg hδ.le hd, mul_le_mul_of_nonneg_right hc1 hh.le]
  · exact qNum_add X p hp N _ _ _ _ (GlobalTheory.T.effQCartierNumEquivMultiple_nonneg_smul X p hp N d (1 - δ) D (by linarith) hQ)
      (GlobalTheory.T.effQCartierNumEquivMultiple_nonneg_smul X p hp N h c B hc.le hBq)
  · rw [← add_assoc]
    exact hcut
  ·
    intro hk
    rw [← add_assoc] at hk
    have h0 := (GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hn (Δ + (1 - δ) • D) B 0 c x' hBc hc.le).1 hk
    rw [zero_smul, add_zero] at h0
    exact hx' δ hδ.le hδb h0

end GlobalTheory.PairStep
