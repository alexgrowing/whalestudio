import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevZeroOfKHighest
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLowestKFiniteVectorDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModuleStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InitialLengthsProductMomentLeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModelStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyProductBoundConstantLeStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyEndomorphismsModularStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyRecursionStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyBoundStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupBesselGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypothesesStatement

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomProdGap

theorem product_moment_first_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (lb ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, lenA k r z (Matrix.of x) (Fin.castLE hl a) ^ 2) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl ν hν hNz
  have hSG := (GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS
  obtain ⟨hG, -, -, -⟩ := hH
  have hKS : PI.KFinSmooth := by
    unfold BranchingSupport.HypsG BranchingSupport.InputsG at hG
    exact hG.1.2.2.1
  obtain ⟨hN, hFam, hSd, hSF⟩ := hS
  have hk : 1 ≤ k := by
    unfold BranchingSupport.Num at hN
    exact hN.1
  have hz : Formalism.QuantumDeterminants.inWb k r z := by
    unfold BranchingSupport.SideG at hSd
    exact hSd.1
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := by
    unfold BranchingSupport.SideG at hSd
    exact hSd.2.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  have hDS : ∀ ν' : Fin (2 * r + k + 1) → ℤ, n1 ν' ≤ q0 →
      (R ν').IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν' a : ℝ)) := by
    intro ν' h'
    unfold BranchingSupport.IsFam at hFam
    exact hFam ν' h'
  have hDG : ∀ ν' : Fin (2 * r + k + 1) → ℤ, n1 ν' ≤ q0 →
      (R ν').IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν' a : ℝ)) := by
    intro ν' h'
    have h2 := hSG
    unfold BranchingSupport.SetupG BranchingSupport.IsFamG at h2
    exact h2.2.1 ν' h'
  obtain ⟨Q, hQ⟩ := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).1 hk
  have hQu : IsUnit Q := by
    unfold PI.UpqRep.IsCayleyU at hQ
    exact ⟨⟨Q, star Q, Matrix.mem_unitaryGroup_iff.mp hQ.2, Matrix.mem_unitaryGroup_iff'.mp hQ.2⟩, rfl⟩
  have hEx : ∀ ν' : Fin (2 * r + k + 1) → ℤ, ∃ E' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E' ∧ Formalism.REAL.GlRel E' := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E', h1, h2⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hKS k r _ _ (R ν') (hDS ν' h') Q hQu
      exact ⟨E', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hEx
  obtain ⟨w, hw1, -, hKH, hfin⟩ := GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries hKS k r _ _ (R ν) (hDS ν hν0) Q (E ν) hQ (hE ν hν0).1
  have hMod := Gp91.GlobalTheory.isMod_smooth_of_isDS hG k r _ _ (R ν) hk (hDG ν hν0) Q (E ν) hQ (hE ν hν0).1
  have hLev : BranchingSupport.Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w := by
    unfold BranchingSupport.IsMod at hMod
    exact GlobalTheory.lev_zero_of_kHighest _ _ _ _ _ _ hMod.1 hMod.2.1 hKH hfin
  have hq4 : ∀ q ≤ (r + 1) ^ 2, 0 + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 := by
    intro q hq
    have h1 : (r + 1) ^ 2 ≤ (2 * r + k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hA : ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) *
      (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (((2 * r + k + 1 : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) ^ q) := by
    intro q hq
    have h1 := Gp91.GlobalTheory.Moment.moment_first_length hG k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ
      (fun ν' h' => hE ν' h') q ν (le_trans (Nat.add_le_add_left hq _) hν) 0 (hq4 q hq) w hLev
    rwa [hw1, one_pow, mul_one] at h1
  have hRr : ∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ /
      lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤
      ENNReal.ofReal ((b ^ 2) ^ (2 * q)) := by
    intro a q hq
    have h1 := Gp91.GlobalTheory.RatioMoment.ratio_moment hG k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ
      (fun ν' h' => hE ν' h') ν hν0 0 q (hq4 q hq) a w hLev
    rwa [hw1, one_pow, mul_one] at h1
  have hdg : 0 < dg ν := (hSF ν hν0).2.1
  have hmass : ∫⁻ x, ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) ∂νq = 1 := by
    have h1 := ((Gp91.GlobalTheory.MomMass.mom_mass hG k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hSG ν hν0).2
      hNz).2 (w : (R ν).H) w.2
    simp only [one_mul] at h1
    rw [h1]
    have h2 : ‖(w : (R ν).H)‖ = 1 := hw1
    rw [h2, one_pow, ENNReal.ofReal_one]
  obtain ⟨hae, -, hlenM, hbesM⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hKS k r _ _ (R ν) Wp z π u μW μN μG νq (hDS ν hν0) hSd
  obtain ⟨hIsBes, -⟩ := (hSF ν hν0).1
  have hPhM : AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) νq :=
    ((hbesM (lb ν) hIsBes (w : (R ν).H) w.2).norm.aemeasurable.pow_const 2).const_mul (dg ν)
  have hpos : ∀ a, ∀ᵐ x ∂νq, 0 < lenA k r z (Matrix.of x) a := fun a =>
    hae.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hz hT (Matrix.of x) hx).2.2.1 a
  have hnf := (GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN).1
  have hb1 : 1 ≤ b := by
    have h1 := hnf.2.2.1
    have h2 : (0 : ℝ) ≤ 2 * r + k := by positivity
    linarith
  have hbv : 0 ≤ bv := by linarith [hnf.2.1]
  have hA0 : 0 ≤ ((2 * r + k + 1 : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hT.le (by positivity))) (pow_nonneg (by linarith) _)
  have key := GlobalTheory.T.initial_lengths_product_moment_le (Formalism.QuantumDeterminants.Mt k r) νq r l hl (fun a x => lenA k r z (Matrix.of x) a)
    (fun x => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) ((2 * r + k + 1 : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2) (fun a => hlenM a) hpos hPhM
    (fun x => mul_nonneg hdg.le (sq_nonneg _)) hmass hA0 (one_le_pow₀ hb1) hA hRr
  refine ⟨(w : (R ν).H), w.2, hw1, le_trans key (ENNReal.ofReal_le_ofReal ?_)⟩
  exact pow_le_pow_left₀ (mul_nonneg hA0 (by positivity))
    (GlobalTheory.T.numericalFamily_productBound_constant_le k r lam u b bv ga h q0 _ hN hT) l

end GlobalTheory.MomProdGap
