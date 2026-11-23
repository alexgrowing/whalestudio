import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemLpAndTendstoIntegralInnerOfEventuallyEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HsInnerSelfEqNormSq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliWordProductDecayBoundUniform
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaCutFTendsto
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCutoffLocalityStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqIntegralInnerTopVectorsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorCutoffEqAndVanishStatement

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem threshold_le_cut (k r N : ℕ) :
    B.AB k r ≤ 3 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) := by
  unfold B.AB
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set D : ℝ := 2 * (r : ℝ) + k + 1 with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have h1 : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ D * D :=
    mul_le_mul (by rw [hD]; linarith) (by rw [hD]; linarith) (by linarith) (by linarith)
  have h2 : D * D ≤ D ^ 3 := by nlinarith [mul_nonneg (mul_self_nonneg D) (sub_nonneg.2 hD1)]
  have h3 : 1 ≤ D ^ 3 := one_le_pow₀ hD1
  have h4 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)
  have h5 : 0 ≤ (N : ℝ) * D ^ 2 := by positivity
  have h6 : (N : ℝ) * D ^ 2 + D ^ 3 ≤ ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * D ^ 2 + D ^ 3) :=
    le_mul_of_one_le_left (by linarith) h4
  nlinarith

theorem integral_topDensity_eq_levelZero : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ((∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)‖ ≤ h c) → ∫ c : Fin (P.r + 1) → ℂ, TBB.Ew p (fun _ => 1) f (P.r + 1) w (TBB.bigPt P.r c) = (p.RR f 0 w [] []).re := by
  intro hXi hA Cb
  obtain ⟨Cc, hCc⟩ := GlobalTheory.T.levelZeroPairing_eq_integral_inner_topVectors hA Cb
  refine ⟨max Cc 3, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hDD hχ hf hCC hthr hw hN hdom
  obtain ⟨-, h, hint, hb⟩ := hdom
  have hX : (0 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by positivity
  have hthr1 : Cc * ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    refine le_trans ?_ hthr
    rw [mul_assoc Cc, mul_assoc (max Cc 3)]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  have hAB : B.AB P.k P.r ≤ A := by
    refine le_trans (threshold_le_cut P.k P.r N) (le_trans ?_ hthr)
    rw [mul_assoc (3 : ℝ), mul_assoc (max Cc 3)]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hX
  have hpol := hCc Wp Wq P p f χ A N w hDD hχ hf hCC hthr1 hw hN
  obtain ⟨δ, hδ, hδχ⟩ := hχ.2.1
  have hcut := fun (ε : ℝ) (hε : 0 < ε) (c : Fin (P.r + 1) → ℂ) =>
    GlobalTheory.T.topVector_cutoff_eq_and_vanish Wp Wq P p Cb χ δ ε f w c hDD hw hχ hδχ hε hf
  set X := List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) f w with hXdef
  have hXCC : B.InCC A 5 X := by
    obtain ⟨K, -, hK⟩ := GlobalTheory.capelli_fold_ccle P.k P.r Wp Wq (M.sgn P p.l0) w 5
    obtain ⟨c, hc⟩ := hCC (5 + List.length w * (2 * P.r + P.k + 1))
    exact ⟨K * c, hK A c f hf hc⟩
  have hlimL := GlobalTheory.beta_cutF_tendsto hXi P.k P.r Wp Wq p.T.base χ A X f hχ hAB hXCC (hCC 5)
  have hlimR := (GlobalTheory.memLp_and_tendsto_integral_inner_of_eventually_eq (Fin (P.r + 1) → ℂ) volume _
    (fun ε => tv p (D.cutF p.T.base χ f ε) w) (tv p f w) h hint
    (Eventually.of_forall fun ε => GlobalTheory.T.aestronglyMeasurable_topVector_smoothCoefficient Wp Wq P p Cb _ w hDD hw
      (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf ε))
    (by
      filter_upwards [hb] with ε hε
      filter_upwards [hε] with c hc
      rw [Ew_eq_norm_tv_sq] at hc
      exact le_trans (le_abs_self _) hc)
    (Eventually.of_forall fun c => by
      by_cases hG : 0 < TBB.Gp p (TBB.bigPt P.r c)
      · filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
        exact (hcut ε hε.1 c).1 hε.2
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε' : 0 < ε := hε
        have hG' := not_lt.1 hG
        rw [(hcut ε hε' c).2.2 hG', (hcut ε hε' c).2.1 (lt_of_le_of_lt hG' (mul_pos hδ hε'))])).2
  have heq : (fun ε : ℝ => B.beta p.T.base X (D.cutF p.T.base χ f ε)) =ᶠ[𝓝[>] 0]
      fun ε : ℝ => ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε) w c) (tv p f w c) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have hδε : 0 < δ * ε := mul_pos hδ hε'
    have h1 : 0 < δ * ε / 2 := by linarith
    have h2 : δ * ε / 2 < δ * ε := by linarith
    rw [hXdef, ← GlobalTheory.T.levelZeroPairing_cutoff_locality Wp Wq P p (M.sgn P p.l0) w χ δ ε (δ * ε / 2) f hχ hδχ hε' h1 h2 hf,
      hpol _ _ h1 hε']
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    by_cases hG : TBB.Gp p (TBB.bigPt P.r c) < δ * ε
    · simp only [(hcut ε hε' c).2.1 hG, inner_zero_left]
    · simp only [(hcut _ h1 c).1 (lt_of_lt_of_le h2 (not_lt.1 hG))]
  have hfin := tendsto_nhds_unique (hlimL.congr' heq) hlimR
  have hRR : p.RR f 0 w [] [] = B.beta p.T.base X f := by
    unfold KB.Pl.RR
    rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hf (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw)]
    rfl
  rw [hRR, hfin, Complex.ofReal_re]
  exact integral_congr_ae (Eventually.of_forall fun c => Ew_eq_norm_tv_sq Wp Wq P p f w c)

end GlobalTheory.TopVec
