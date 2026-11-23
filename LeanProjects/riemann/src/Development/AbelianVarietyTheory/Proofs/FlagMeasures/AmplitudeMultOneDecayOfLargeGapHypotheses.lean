import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocInOfUniqOfDecLow

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalInputsGap

open GlobalTheory.Amp.LocalInputs

theorem multOne_of_uniqGap (hU : GlobalTheory.GapIn.UniqGap) {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mat k r → (Wp →L[ℂ] Wp)} {h : ℝ}
    (hk : 1 ≤ k) (hg : GapAtLeast ε lam h) (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h)
    (hl : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (hz : inWb k r z) (hT : 0 < Tz k r z) (hc : c ≠ 0)
    (hπ : IsHCTypeW k r z u π) : MultOne z (psi k r z c) σ π := by
  intro B B' h1 h'
  rw [GlobalTheory.BesselMultOne.psi_eq_psiGen] at h1 h'
  obtain ⟨a, b, hab, e⟩ := hU k r ε lam h H σ z (fun _ => c) u Wp π hk hg hh hl hσ hz hT (fun _ => hc) hπ B B'
    (GlobalTheory.BesselMultOne.isBesselMapSm_of h1) (GlobalTheory.BesselMultOne.isBesselMapSm_of h')
  rcases hab with ha | hb
  · refine ⟨-(a⁻¹ * b), Or.inl fun v hv => ?_⟩
    have h3 : a • B v = -(b • B' v) := eq_neg_of_add_eq_zero_left (e v hv)
    rw [neg_smul, mul_smul, ← smul_neg, ← h3, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · refine ⟨-(b⁻¹ * a), Or.inr fun v hv => ?_⟩
    have h3 : b • B' v = -(a • B v) := eq_neg_of_add_eq_zero_right (e v hv)
    rw [neg_smul, mul_smul, ← smul_neg, ← h3, smul_smul, inv_mul_cancel₀ hb, one_smul]

theorem gap_small_le {k r : ℕ} (hk : 1 ≤ k) :
    120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 19 := by
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn2 : 2 ≤ n := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) ≤ r := by positivity
    rw [hn]; push_cast; linarith
  have h16 : (120 : ℝ) ≤ n ^ 16 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn2 16)
  have : n ^ 19 = n ^ 16 * n ^ 3 := by ring
  rw [this]; gcongr

theorem locIn_of_hypGap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), Big D large₂ Cl m₀ → LocIn D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH Cg cb Cu cT CT C0
  have hU : GlobalTheory.GapIn.UniqGap := hH.2.1
  have hD : Formalism.FourierDecayAlt.ThreeDimData.DecLow := hH.1.1.1
  refine ⟨0, fun D large₂ C' Cl hB hZ τ w w' θ W hTT hW A hA => ?_⟩
  obtain ⟨c1, c2, z1, z2, t1, t2, -⟩ := hW
  obtain ⟨hl, hds, -, -, -, -, ⟨P, hP, hv⟩, -⟩ := hA
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv1, -, hgap, -, -, -, hCl⟩, -, -⟩ := hZ
  have hT1 : 0 < Tz D.R.k D.R.rS W.z := by
    rw [t1]; unfold Tr; exact_mod_cast hTT.1.pos
  have hT2 : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [t2]; unfold Tr; exact_mod_cast hTT.2.1.pos
  have hc : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    have g0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
    have g1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
    have hka : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
    exact Complex.ofReal_ne_zero.2 (by positivity)
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hmf : (D.R.m : ℝ) ≤ D.R.f := by exact_mod_cast D.R.m_le_f
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hf5 : (D.R.m : ℝ) ≤ (D.R.f : ℝ) ^ 5 := hmf.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hge : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    rw [dimS_eq]
    calc (D.R.r : ℝ) ^ 19 = 1 * (D.R.r : ℝ) ^ 19 * 1 := by ring
      _ ≤ (Cl * D.R.m) * (D.R.r : ℝ) ^ 19 * large₂.sc.L := by gcongr; exact hB.2.1
      _ ≤ (Cl * (D.R.f : ℝ) ^ 5) * (D.R.r : ℝ) ^ 19 * large₂.sc.L := by gcongr
      _ = _ := by ring
  have hg := gap_of_nodes D τ _ hl.1 fun j h1 h2 => hge.trans (hgap τ j h1 h2)
  have hh := gap_small_le (r := D.R.rS) hk
  refine ⟨multOne_of_uniqGap hU hk hg hh hl hds z1 hT1 hc c1,
    multOne_of_uniqGap hU hk hg hh hl hds z2 hT2 hc c2, ?_⟩
  refine (decay_span (by positivity) (urep_of_ds hds) (decay_low hD hk hl hds hg hP)).mono ?_
  exact Submodule.span_mono fun v ⟨g, hg, e⟩ => ⟨g, hg, _, hv, e⟩

end GlobalTheory.Amp.LocalInputsGap
