import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiscreteSeriesDegreeBound
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyStatementOfAbsAndVandermonde
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdDiffEqProdFactorial
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraFormalDegreeCompactDualLargeGapsStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DegLine

open Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem gap_near {N : ℕ} (ε : Fin N → Bool) (l ν : Fin N → ℝ) (G ρ : ℝ) (hg : GapAtLeast ε l G)
    (hν : l1dist ν l ≤ ρ) : GapAtLeast ε ν (G - 2 * ρ) := by
  intro a b hab
  have hco : ∀ j, |ν j - l j| ≤ ρ := fun j =>
    le_trans (Finset.single_le_sum (f := fun j => |ν j - l j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)) hν
  have h1 := hg a b hab
  have h2 := hco a
  have h3 := hco b
  have h4 : |l a - l b| ≤ |ν a - ν b| + |ν a - l a| + |ν b - l b| := by
    have e : l a - l b = (ν a - ν b) - (ν a - l a) + (ν b - l b) := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (by have := abs_sub (ν a - ν b) (ν a - l a); linarith)
  linarith

theorem gap_lamD (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) :
    GapAtLeast (epsSH D.R) (lamD D τ) (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbnd, _, _, _, _, hstep, _, _, _, hCl⟩ := hH.1
  have hL := one_lt_scL large₂
  have hG0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have : 0 ≤ Cl := hCl.le
    have : 0 ≤ large₂.sc.L := by linarith
    positivity
  have hv : ∀ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l := fun l h1 h2 => (hH.2.1.1 τ l h1 h2).1
  have hm := D.R.two_le_m
  have hb1 : 0 ≤ bOne D τ 1 := by
    have h := (hbnd τ 1 le_rfl (by omega)).1
    exact le_trans (le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) (le_max_left _ _)) h
  have g := gapAtLeast_of τ _ hG0 hv hb1 (hstep τ)
  intro a b hab
  exact g (Fin.cast (dimS_eq D.R) a) (Fin.cast (dimS_eq D.R) b) hab

theorem deg_eq_fdegHC (D : D7) (ht : cdScaleTie D) {W : LocW D.R.k D.R.rS}
    (l : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (hA : GoodS D l A) (h : ℝ)
    (hg : GapAtLeast (epsSH D.R) l h) (hth : Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h) : A.deg = fdegHC l := by
  obtain ⟨P, hP, hd⟩ := hA.2.2.2.2.2.2.2.2.2.2
  obtain ⟨Q, ⟨hQ, -⟩, hDS⟩ := hA.2.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  let u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ := ⟨Q * P⁻¹, P * Q⁻¹,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩
  let a : Formalism.REAL.UJ (epsSH D.R) := ⟨u, GlobalTheory.FormalDegreeDatum.inUJ_of_cayley _ P Q _ hP.1 hP.2 hQ.2⟩
  have hsc := (GlobalTheory.Mem.Vol.cdScaleTie_iff D).1 ht
  obtain ⟨a1, b1, hab⟩ := Formalism.MainNotions.TheoremBConstants.epsSH_both D
  have ht1 : ∃ x, epsSH D.R x = true := by
    cases h1 : epsSH D.R a1
    · exact ⟨b1, by cases h2 : epsSH D.R b1 <;> simp_all⟩
    · exact ⟨a1, h1⟩
  have hf1 : ∃ x, epsSH D.R x = false := by
    cases h1 : epsSH D.R a1
    · exact ⟨a1, h1⟩
    · exact ⟨b1, by cases h2 : epsSH D.R b1 <;> simp_all⟩
  have hF := GlobalTheory.T.harishChandra_formalDegree_compactDual_large_gaps D.cd D.s.cdScale hsc _ (epsSH D.R) l h hA.1 ht1 hf1 hg hth A.H
    (fun g => A.σ (Q⁻¹ * g * Q)) hDS
  haveI := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : A.H)
  have h2 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj _ (fun g => A.σ (P⁻¹ * g * P))
    (fun g => A.σ (Q⁻¹ * g * Q)) a (fun g => by
      have e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹) := rfl
      have e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q =
          (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q) := by
        simp only [Matrix.mul_assoc]
      simp only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 A.deg hd w hw
  have h3 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj _ (fun g => A.σ (Q⁻¹ * g * Q))
    (fun g => A.σ (Q⁻¹ * g * Q)) 1 (fun g => by simp) hDS.2.2.1 (fdegHC l) hF w hw
  exact h2.symm.trans h3

theorem deg_eq_near (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 Cn : ℝ} (hCl : 2 * |Cn| + 8 ≤ Cl)
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (ht : cdScaleTie D) (τ : D.what₂.Tau) {W : LocW D.R.k D.R.rS}
    (ν : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (hν : l1dist ν (lamD D τ) ≤ |Cn| * (D.R.r : ℝ) ^ 4 + D.R.r)
    (A : LocS W) (hA : GoodS D ν A) : A.deg = fdegHC ν := by
  refine deg_eq_fdegHC D ht ν A hA _ (gap_near _ _ _ _ _ (gap_lamD D large₂ hH τ) hν) ?_
  obtain ⟨_, _, hmf, _⟩ := hH.1
  have hL := one_lt_scL large₂
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr6 : (6 : ℝ) ≤ D.R.r := by
    have : 6 ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; omega
    exact_mod_cast this
  have hthr := Formalism.MainNotions.GapDS.thrE_le (epsSH D.R) (by rw [Formalism.MainNotions.BridgeLemma₂.deg_cast_r]; linarith)
  rw [Formalism.MainNotions.BridgeLemma₂.deg_cast_r] at hthr
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ D.R.r := by linarith
  have h419 : (D.R.r : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have h319 : (D.R.r : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have h119 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by
    simpa using pow_le_pow_right₀ hn1 (show 1 ≤ 19 by norm_num)
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  have hfl : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 * large₂.sc.L := by nlinarith
  have hCl0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_nonneg (by linarith [abs_nonneg Cn]) (by positivity)
  have e1 : Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have := mul_le_mul_of_nonneg_left hfl hCl0
    have e : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L = Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) := by
      ring
    rw [e]; linarith
  have e2 : (2 * |Cn| + 8) * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 :=
    mul_le_mul_of_nonneg_right hCl (by positivity)
  have e3 : |Cn| * (D.R.r : ℝ) ^ 4 ≤ |Cn| * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_left h419 (abs_nonneg _)
  nlinarith

theorem deg_VandLine_of_gap : ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 : ℝ),
    thr ≤ C' → thr ≤ Cl → Ties D → Formalism.MainNotions.BridgeLemma₂.deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 := by
  intro Cn
  refine ⟨2 * |Cn| + 8, fun D large₂ C' Cl Cg cb Cu cT CT C0 C1 _ hCl hT => ?_⟩
  intro hH τ w w' _ θ _ W _ lam' hl A hA I s hs A' hA'
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have : D.R.k ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; omega
    exact_mod_cast this
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by
    have : D.R.m ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; omega
    exact_mod_cast this
  have hn : (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 4 := by
    calc (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) * (D.R.r : ℝ) ^ 3 :=
          mul_le_mul hkr (pow_le_pow_left₀ (by positivity) hmr 3) (by positivity) (by positivity)
      _ = (D.R.r : ℝ) ^ 4 := by ring
  have hcard : (I.card : ℝ) ≤ D.R.r := by
    rw [← Formalism.MainNotions.BridgeLemma₂.deg_cast_r]
    have : I.card ≤ 2 * D.R.rS + D.R.k + 1 := by
      have := Finset.card_le_univ I
      rwa [Fintype.card_fin] at this
    exact_mod_cast this
  have hl' : Cn * D.R.k * (D.R.m : ℝ) ^ 3 ≤ |Cn| * (D.R.r : ℝ) ^ 4 := by
    have e : Cn * D.R.k * (D.R.m : ℝ) ^ 3 = Cn * ((D.R.k : ℝ) * (D.R.m : ℝ) ^ 3) := by ring
    rw [e]
    exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self Cn) (by positivity))
      (mul_le_mul_of_nonneg_left hn (abs_nonneg _))
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have h1 : l1dist lam' (lamD D τ) ≤ |Cn| * (D.R.r : ℝ) ^ 4 + D.R.r := by linarith
  have h2 : l1dist (lam' + s • epsI I) (lamD D τ) ≤ |Cn| * (D.R.r : ℝ) ^ 4 + D.R.r :=
    le_trans (Formalism.MainNotions.BridgeLemma.l1_distance_sign_step _ _ s hs I) (by linarith)
  rw [deg_eq_near D large₂ hCl hH hT.cdScale_tie τ lam' h1 A hA,
    deg_eq_near D large₂ hCl hH hT.cdScale_tie τ _ h2 A' hA']

end GlobalTheory.DegLine
