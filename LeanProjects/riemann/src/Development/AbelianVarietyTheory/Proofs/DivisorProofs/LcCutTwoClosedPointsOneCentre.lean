import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultNsmulOfQadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtAddSmulOfLcAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltAtPointsNotContainingCentreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalLogCanonicalThresholdAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonKltLocusDimLtAfterPerturbationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffQCartierNumEquivMultipleNonnegSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectiveQCartierDivisorConvexConeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem logCanonicalCut_two_points : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (d h : ℚ) (x x' z : X) (j : ℕ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → QNum p N d D → 0 ≤ d → IsClosed ({x} : Set X) → IsClosed ({x'} : Set X) → LcAt p n (Δ + D) x → LcAt p n (Δ + D) x' → z ⤳ x → z ⤳ x' → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) → 0 < h → 2 * ((j + 1 : ℕ) : ℚ) ^ (j + 1) < h ^ (j + 1) * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin (j + 1) => N : ℤ) → ∃ (D' : X → ℚ) (d' : ℚ), 0 ≤ d' ∧ d' ≤ d + h ∧ QNum p N d' D' ∧ ((LcCut p n (Δ + D') x j ∧ ¬ KltAt p n (Δ + D') x') ∨ (LcCut p n (Δ + D') x' j ∧ ¬ KltAt p n (Δ + D') x)) := by
  intro hPr hNa hNe X _ _ _ p n hp hn
  letI := algebraΓOfHom p
  intro Δ m G N D d h x x' z j hΔ hklt hm hG hN hD hd hx hx' hlx hlx' hzx hzx' hz hdim hh hpos
  classical
  have hDq : IsQCart D := hD.isQCart
  obtain ⟨B, δ₀, hδ0, hδ1, hB, hoff, hnk, hpres⟩ :=
    GlobalTheory.T.exists_divisor_nonKlt_at_points_not_containing_centre hPr hNa hNe X p n hp hn Δ m G N D {x, x'} z (j + 1) h hΔ hklt hm hG hN hDq
      (by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact ⟨hx, hzx⟩
        · rw [Finset.mem_singleton.1 hy]; exact ⟨hx', hzx'⟩)
      (by omega) hdim hz hh
      (by
        have hc : (({x, x'} : Finset X).card : ℚ) ≤ 2 := by
          exact_mod_cast Finset.card_le_two
        have hk : (0 : ℚ) ≤ ((j + 1 : ℕ) : ℚ) ^ (j + 1) := by positivity
        calc (({x, x'} : Finset X).card : ℚ) * ((j + 1 : ℕ) : ℚ) ^ (j + 1)
            ≤ 2 * ((j + 1 : ℕ) : ℚ) ^ (j + 1) := mul_le_mul_of_nonneg_right hc hk
          _ < _ := hpos)
  have hBq : IsQCart B := hB.isQCart
  have hδ1' : (0 : ℚ) ≤ 1 - δ₀ := by linarith
  have hDδ : IsQCart ((1 - δ₀) • D) := (GlobalTheory.T.isEffectiveQCartierDivisor_convexCone X D D (1 - δ₀) hDq hDq hδ1').2.1
  have hkx : KltAt p n (Δ + (1 - δ₀) • D) x :=
    GlobalTheory.T.kltAt_add_one_sub_smul_of_kltAt_of_lcAt X p n hp hn Δ D δ₀ x hDq (hklt x) hlx hδ0 hδ1
  have hkx' : KltAt p n (Δ + (1 - δ₀) • D) x' :=
    GlobalTheory.T.kltAt_add_one_sub_smul_of_kltAt_of_lcAt X p n hp hn Δ D δ₀ x' hDq (hklt x') hlx' hδ0 hδ1
  obtain ⟨c, hc0, hc1, hcl, hcn⟩ := GlobalTheory.T.exists_rational_logCanonicalThreshold_at_point hPr X p n hp hn Δ m G ((1 - δ₀) • D) B x hm hG hDδ
    hBq hkx (hnk δ₀ hδ0.le le_rfl x (by simp))
  obtain ⟨c', hc0', hc1', hcl', hcn'⟩ := GlobalTheory.T.exists_rational_logCanonicalThreshold_at_point hPr X p n hp hn Δ m G ((1 - δ₀) • D) B x' hm hG
    hDδ hBq hkx' (hnk δ₀ hδ0.le le_rfl x' (by simp))
  have hq1 : QNum p N ((1 - δ₀) * d) ((1 - δ₀) • D) := GlobalTheory.T.effQCartierNumEquivMultiple_nonneg_smul X p hp N d (1 - δ₀) D hδ1' hD
  have key : ∀ e : ℚ, 0 < e → e ≤ 1 → ∃ d' : ℚ, 0 ≤ d' ∧ d' ≤ d + h ∧
      QNum p N d' ((1 - δ₀) • D + e • B) := by
    intro e he0 he1
    refine ⟨(1 - δ₀) * d + e * h, by positivity, by nlinarith, ?_⟩
    exact qNum_add X p hp N _ _ _ _ hq1 (GlobalTheory.T.effQCartierNumEquivMultiple_nonneg_smul X p hp N h e B he0.le hB)
  rcases le_total c' c with hcc | hcc
  · obtain ⟨d', h1, h2, h3⟩ := key c hc0 hc1
    refine ⟨(1 - δ₀) • D + c • B, d', h1, h2, h3, Or.inl ⟨?_, ?_⟩⟩
    · rw [← add_assoc]
      exact GlobalTheory.T.nonKlt_locus_dim_lt_after_perturbation X p n hp hn Δ D B δ₀ c x z j (hklt x) hDq hBq hlx hδ0 hδ1 hc1 hoff hpres
        hdim hcl hcn
    · rw [← add_assoc]
      intro hk
      exact hcn' ((GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hn (Δ + (1 - δ₀) • D) B c' c x' hBq hcc).1 hk)
  · obtain ⟨d', h1, h2, h3⟩ := key c' hc0' hc1'
    refine ⟨(1 - δ₀) • D + c' • B, d', h1, h2, h3, Or.inr ⟨?_, ?_⟩⟩
    · rw [← add_assoc]
      exact GlobalTheory.T.nonKlt_locus_dim_lt_after_perturbation X p n hp hn Δ D B δ₀ c' x' z j (hklt x') hDq hBq hlx' hδ0 hδ1 hc1' hoff
        hpres hdim hcl' hcn'
    · rw [← add_assoc]
      intro hk
      exact hcn ((GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hn (Δ + (1 - δ₀) • D) B c c' x hBq hcc).1 hk)

end GlobalTheory.PairStep
