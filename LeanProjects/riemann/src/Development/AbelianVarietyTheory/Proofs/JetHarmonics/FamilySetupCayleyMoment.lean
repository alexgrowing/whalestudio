import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlProjectionLevelSumSqLeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentGrowthStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyWeightedStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsModularStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentEstimateStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorBesselTransferStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModelStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormSqHermTranslatesOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriTensorDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomentStep

theorem lintegral_le_of_le_sum {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (f : Ω → ℝ)
    (g : ι → ι → Ω → ℝ) (C : ℝ) (N : ι → ι → ℝ) (hC : 0 ≤ C) (hg0 : ∀ d s x, 0 ≤ g d s x)
    (hm : ∀ d s, AEMeasurable (g d s) ν) (hpt : ∀ᵐ x ∂ν, f x ≤ C * ∑ d, ∑ s, g d s x)
    (hN : ∀ d s, 0 ≤ N d s) (hint : ∀ d s, ∫⁻ x, ENNReal.ofReal (g d s x) ∂ν ≤ ENNReal.ofReal (N d s)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ENNReal.ofReal (C * ∑ d, ∑ s, N d s) := by
  calc ∫⁻ x, ENNReal.ofReal (f x) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal C * ∑ d, ∑ s, ENNReal.ofReal (g d s x) ∂ν := by
        refine lintegral_mono_ae (hpt.mono fun x hx => ?_)
        refine (ENNReal.ofReal_le_ofReal hx).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg fun d _ => Finset.sum_nonneg fun s _ => hg0 d s x]
        congr 1
        exact Finset.sum_congr rfl fun d _ => ENNReal.ofReal_sum_of_nonneg fun s _ => hg0 d s x
    _ = ENNReal.ofReal C * ∑ d, ∑ s, ∫⁻ x, ENNReal.ofReal (g d s x) ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finset_sum' _ fun d _ => Finset.aemeasurable_fun_sum _ fun s _ => (hm d s).ennreal_ofReal]
        congr 1
        exact Finset.sum_congr rfl fun d _ => lintegral_finset_sum' _ fun s _ => (hm d s).ennreal_ofReal
    _ ≤ ENNReal.ofReal C * ∑ d, ∑ s, ENNReal.ofReal (N d s) := by
        gcongr with d _ s _
        exact hint d s
    _ = _ := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg fun d _ => Finset.sum_nonneg fun s _ => hN d s]
        congr 1
        exact (Finset.sum_congr rfl fun d _ => ENNReal.ofReal_sum_of_nonneg fun s _ => hN d s).symm

theorem norm_sum_smul_sq_le {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (c : ι → ℂ)
    (v : ι → V) : ‖∑ s, c s • v s‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ s, ‖c s‖ ^ 2 * ‖v s‖ ^ 2 := by
  have h1 : ‖∑ s, c s • v s‖ ≤ ∑ s, ‖c s‖ * ‖v s‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => norm_smul _ _))
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun s => ‖c s‖ * ‖v s‖)
  simp only [mul_pow, Finset.card_univ] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem pointwise_le {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (L D A : ℝ) (q : ℕ)
    (a β : ι → ℂ) (Ds : ι → ℝ) (v : V) (y : ι → ι → V) (hD : 0 ≤ D) (hL : ∑ d, ‖a d‖ ^ 2 = L ^ 2)
    (he : ∀ d, a d • v = ∑ s, β s • y d s) (hβ : ∀ s, ‖β s‖ ^ 2 * D ≤ A * Ds s) :
    L ^ (2 * (q + 1)) * (D * ‖v‖ ^ 2) ≤
      ((Fintype.card ι : ℝ) * A) * ∑ d, ∑ s, L ^ (2 * q) * (Ds s * ‖y d s‖ ^ 2) := by
  have hP : 0 ≤ L ^ (2 * q) := by rw [pow_mul]; positivity
  have e1 : L ^ (2 * (q + 1)) * (D * ‖v‖ ^ 2) = ∑ d, L ^ (2 * q) * (D * ‖a d • v‖ ^ 2) := by
    rw [mul_add, pow_add, mul_one, ← hL, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [norm_smul]; ring
  rw [e1, Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [he d]
  calc L ^ (2 * q) * (D * ‖∑ s, β s • y d s‖ ^ 2)
      ≤ L ^ (2 * q) * (D * ((Fintype.card ι : ℝ) * ∑ s, ‖β s‖ ^ 2 * ‖y d s‖ ^ 2)) := by
        gcongr
        exact norm_sum_smul_sq_le β (y d)
    _ = ∑ s, (Fintype.card ι : ℝ) * L ^ (2 * q) * ‖y d s‖ ^ 2 * (‖β s‖ ^ 2 * D) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ∑ s, (Fintype.card ι : ℝ) * L ^ (2 * q) * ‖y d s‖ ^ 2 * (A * Ds s) := by
        exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hβ s) (by positivity)
    _ = _ := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring

theorem lOneNorm_sub_single_one_le {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) : n1 (ν - Pi.single s 1) ≤ n1 ν + 1 := by
  have h1 : ∑ i, ((Pi.single s 1 : Fin n → ℤ) i).natAbs = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  unfold n1
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_sub_le _ _

theorem param_sub_single {n : ℕ} (lam : Fin n → ℝ) (ν : Fin n → ℤ) (s : Fin n) :
    (fun a => lam a + (((ν - Pi.single s 1) : Fin n → ℤ) a : ℝ)) =
      (fun a => lam a + (ν a : ℝ)) - Pi.single s 1 := by
  funext a
  by_cases h : a = s
  · subst h; simp; ring
  · simp [h]

set_option maxHeartbeats 1000000 in

theorem moment_step : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν + 1 ≤ q0 → ∀ (j q : ℕ) (MM : ℝ), j ≤ 4 * (2 * r + k + 1) ^ 2 → 0 ≤ MM → (∀ (s : Fin (2 * r + k + 1)) (y : (R (ν - Pi.single s 1)).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E (ν - Pi.single s 1)) (fun a => lam a + (((ν - Pi.single s 1) : Fin (2 * r + k + 1) → ℤ) a : ℝ)) (j + 2) y → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg (ν - Pi.single s 1) * ‖l (ν - Pi.single s 1) ((R (ν - Pi.single s 1)).σ (Matrix.of x) y)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (MM * ‖y‖ ^ 2)) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * MM * ‖w‖ ^ 2) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν j q MM hj hMM hind w hw
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hNum, hFam, hG, hSide⟩ := id hS
  have hν0 : n1 ν ≤ q0 := by omega
  have hνs : ∀ s, n1 (ν - Pi.single s 1) ≤ q0 := fun s => (lOneNorm_sub_single_one_le ν s).trans hν
  have hDS := hFam ν hν0
  have hDSs := fun s => hFam _ (hνs s)
  obtain ⟨hBe, hdg, -⟩ := hSide ν hν0
  have hBes := fun s => (hSide _ (hνs s)).1
  have hdgs := fun s => (hSide _ (hνs s)).2.1
  obtain ⟨hae, -, hmL, hml⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG
  by_cases hnz : NzOn (R ν) (l ν)
  swap
  · have : ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) *
        (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = 0 := by
      rw [← lintegral_zero (μ := νq)]
      refine lintegral_congr_ae (hae.mono fun x hx => ?_)
      have : l ν ((R ν).σ (Matrix.of x) w) = 0 := by
        by_contra hne
        exact hnz ⟨_, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate hDS.2 w.2 hx, hne⟩
      simp [this]
    rw [this]
    exact bot_le
  obtain ⟨io, pr, ep, hT⟩ := (GlobalTheory.T.pieri_tensor_decomposition hH k r lam u b bv ga h q0 R hNum hFam ν).2 hν
  have hF := GlobalTheory.isFRep_dualM k r
  have hkap := fun s => GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν)
    (fun s => R (ν - Pi.single s 1)) io pr ep _ _ _ Wp z π u μW μN μG νq
    (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (l ν) hDS hDSs hF hT hG
    (fun s hs => (GlobalTheory.FlagFix.fixes_wedge_and_form k r z hG.1 s hs).2) hBe hnz s
    (l (ν - Pi.single s 1)) (hBes s)
  choose κ hκ using fun s => (hkap s).1
  have hdual := fun s => (hkap s).2 (κ s) (hκ s)
  have hA : ∀ s, ‖(ep s : ℂ) * star (κ s)‖ ^ 2 * dg ν ≤
      (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * dg (ν - Pi.single s 1) := by
    intro s
    have h1 := GlobalTheory.T.lowering_scalar_sq_mul_degree_ratio_le hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz s
      (κ s) (hκ s)
    rw [div_le_iff₀ (hdgs s)] at h1
    have h2 : ‖(ep s : ℂ) * star (κ s)‖ = ‖κ s‖ := by
      rcases hT.ep_sq s with h | h <;> simp [h]
    rwa [h2]
  obtain ⟨io', pr', hAlg, hpr⟩ := GlobalTheory.T.dual_tensor_cayley_weighted hK k r _ _ (R ν) hDS (fun s => R (ν - Pi.single s 1)) _ io pr ep Q
    (E ν) (fun s => E (ν - Pi.single s 1)) hDSs hT hQ (hE ν hν0).1 (fun s => (hE _ (hνs s)).1)
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hNum.1 hDS Q (E ν) hQ (hE ν hν0).1
  have hMods : ∀ s, IsMod (PI.BesselPeriodGGP.eps48 k r) (E (ν - Pi.single s 1))
      ((fun a => lam a + (ν a : ℝ)) - Pi.single s 1) := fun s => by
    rw [← param_sub_single]
    exact GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ _ hNum.1 (hDSs s) Q _ hQ (hE _ (hνs s)).1
  have hShape := ((GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum).2 ν hν0).2.1
  have hlev := GlobalTheory.T.unitaryGl_projection_level_sum_sq_le _ _ _ (E ν) (fun s => (R (ν - Pi.single s 1)).smSub) (fun s => E (ν - Pi.single s 1))
    io' pr' _ k j bv w hMod hMods hAlg hShape hj hw
  have hexp : 2 * r + k + 1 + 1 - k = 2 * r + 2 := by omega
  rw [hexp] at hlev
  have hy : ∀ d s, ((pr' s (Pi.single d w) : (R (ν - Pi.single s 1)).smSub) : (R (ν - Pi.single s 1)).H) =
      ∑ c, pr s c (tm (R ν) (fun c => Q d c) w c) := by
    intro d s
    rw [hpr]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [Finset.sum_eq_single d]
    · simp [tm]
    · intro e _ he; simp [he]
    · simp
  have hA0 : 0 ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := mul_nonneg hG.2.1.le (by positivity)
  have key := lintegral_le_of_le_sum νq
    (fun x => lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2))
    (fun d s x => lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg (ν - Pi.single s 1) *
      ‖l (ν - Pi.single s 1) ((R (ν - Pi.single s 1)).σ (Matrix.of x)
        (pr' s (Pi.single d w) : (R (ν - Pi.single s 1)).smSub))‖ ^ 2))
    ((Fintype.card (Fin (2 * r + k + 1)) : ℝ) * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4))
    (fun d s => MM * ‖pr' s (Pi.single d w)‖ ^ 2) (by positivity)
    (fun d s x => mul_nonneg (by rw [pow_mul]; positivity) (mul_nonneg (hdgs s).le (by positivity)))
    (fun d s => ((hmL 0).pow_const _).mul
      ((((GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ _ Wp z π u μW μN μG νq (hDSs s) hG).2.2.2 _ (hBes s).1 _
        (pr' s (Pi.single d w)).2).norm.aemeasurable.pow_const _).const_mul _))
    (hae.mono fun x hx => by
      refine pointwise_le _ _ _ q
        (fun d => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (dualM (Matrix.of x) *ᵥ (fun c => Q d c))
          (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)))
        (fun s => (ep s : ℂ) * star (κ s)) _ _ _ hdg.le ?_ (fun d => ?_) hA
      · rw [GlobalTheory.T.sum_norm_sq_herm_translates_orthonormal k r _ dualM _ Q 1 _ hF hQ.2 _ hx]
        exact (GlobalTheory.TensLen.lengths k r z hG.1 hG.2.1 _ hx).2.1
      · simp only [hy]
        exact GlobalTheory.T.tensor_bessel_transfer hK k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν) (fun s => R (ν - Pi.single s 1)) io pr _ _ _
          Wp _ (l ν) (fun s => l (ν - Pi.single s 1)) _ hDS hDSs hT.raw hBe.1.1 hBe.1.2.1 hdual _ w w.2 _ hx)
    (fun d s => by positivity)
    (fun d s => hind s _ (by rw [param_sub_single]; exact (hlev d).1 s))
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsum : ∑ d, ∑ s, MM * ‖pr' s (Pi.single d w)‖ ^ 2 ≤
      ∑ _d : Fin (2 * r + k + 1), MM * ((6 * bv) ^ (2 * (2 * r + 2)) * ‖w‖ ^ 2) := by
    refine Finset.sum_le_sum fun d _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hlev d).2 hMM
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.MomentStep
