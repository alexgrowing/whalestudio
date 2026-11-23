import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AbsOfRange
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionalSideGrowth
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepOnePlusDet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupBesselGrowth
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContinuousOnOfSmoothOnH
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBesselStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHypsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesBesselGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusCommutesWithUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypesSumStatement

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.AmpMoments

theorem lenA_mul {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (t x : MatKR k r) (s : Fin (r + 1) → ℂ)
    (hs : ∀ a, s a ≠ 0) (ht : ∀ a, t⁻¹ *ᵥ fvec k r z a = s a • fvec k r z a) (a : Fin (r + 1)) :
    lenA k r z (t * x) a = ‖s a‖ * lenA k r z x a := by
  have e : ∀ b, (WithLp.toLp 2 ((t * x)⁻¹ *ᵥ fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1))) =
      s b • WithLp.toLp 2 (x⁻¹ *ᵥ fvec k r z b) := fun b => by
    rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul, WithLp.toLp_smul]
  unfold lenA
  simp only [e]
  set v : Fin (r + 1) → EuclideanSpace ℂ (Fin (2 * r + k + 1)) := fun b => WithLp.toLp 2 (x⁻¹ *ᵥ fvec k r z b)
  have hsp : Submodule.span ℂ ((fun b => s b • v b) '' {b | b < a}) = Submodule.span ℂ (v '' {b | b < a}) := by
    apply le_antisymm <;> refine Submodule.span_le.2 ?_ <;> rintro _ ⟨b, hb, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · have := Submodule.smul_mem (Submodule.span ℂ ((fun b => s b • v b) '' {b | b < a})) (s b)⁻¹
        (Submodule.subset_span ⟨b, hb, rfl⟩)
      simp only [smul_smul, inv_mul_cancel₀ (hs b), one_smul] at this
      exact this
  rw [hsp, ← infDist_smul₀ (hs a)]
  congr 1
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (hs a)]
  exact ((Submodule.smul_mem_iff _ (inv_ne_zero (hs a)))).symm

theorem lintegral_translate {k r : ℕ} (ν : Measure (Mt k r)) (t : MatKR k r) (ht : IsUnit t.det)
    (F : Mt k r → ℝ≥0∞) :
    ∫⁻ y, F y ∂ν = ∫⁻ x, F (fun i j => (t * Matrix.of x) i j) ∂(ν.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) := by
  have hc : ∀ g : MatKR k r, Continuous fun x : Mt k r => (fun i j => (g * Matrix.of x) i j : Mt k r) := fun g =>
    (continuous_const.matrix_mul continuous_id : Continuous fun x : MatKR k r => g * x)
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x) i j
      invFun := fun x => fun i j => (t * Matrix.of x) i j
      left_inv := fun x => (Matrix.mul_nonsing_inv_cancel_left t (Matrix.of x) ht :)
      right_inv := fun x => (Matrix.nonsing_inv_mul_cancel_left t (Matrix.of x) ht :)
      continuous_toFun := hc _
      continuous_invFun := hc _ }
  have := lintegral_map_equiv (μ := ν) (fun x => F (e.symm x)) e.toMeasurableEquiv
  refine Eq.trans ?_ this.symm
  exact lintegral_congr fun y => congrArg F (e.symm_apply_apply y).symm

theorem sq_nnnorm {V : Type} [NormedAddCommGroup V] (v : V) : (‖v‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]; rfl

theorem moment_of_bessel (hH : Hyps) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {μW μN μG νq : Measure (Mt k r)}
    {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r} {l : ∀ ν, (R ν).H → Wp} {dg : (Fin (2 * r + k + 1) → ℤ) → ℝ}
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R l dg) (ν) (q : ℕ) (h1 : n1 ν + (r + 1) * q ≤ q0)
    (h2 : (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2) (R0 : Rep k r) (hR : R ν = R0) (B : R0.H → Wp)
    (hB : IsBes R0 z π B) (v : R0.H) (hv : v ≠ 0)
    (hlow : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P ∧
      v ∈ PI.UpqRep.lowKSub (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (fun g => R0.σ (P⁻¹ * g * P)))
    (h0 : l2SG νq (fun g => B (R0.σ g v)) ≠ 0) (ht : l2SG νq (fun g => B (R0.σ g v)) ≠ ⊤) (a : Fin (r + 1)) :
    ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q)) * (‖B (R0.σ (Matrix.of x) v)‖₊ : ℝ≥0∞) ^ 2 ∂νq ≤
      ENNReal.ofReal (Hsq r (Tz k r z) b ^ q) * l2SG νq (fun g => B (R0.σ g v)) := by
  subst hR
  have hν : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) h1
  obtain ⟨hNum, hFam, hSide, hSF⟩ := id hS
  obtain ⟨⟨-, -, -, -, hOK⟩, hfam⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  obtain ⟨-, -, hgap, -⟩ := hfam ν hν
  have hDS := hFam ν hν
  obtain ⟨hBe, hpos, -⟩ := hSF ν hν
  obtain ⟨-, -, -, hsm, hTK, -, hKT, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r _ _ (R ν) hDS
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w : (R ν).H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hvw : v = ((‖v‖ : ℝ) : ℂ) • w := by
    rw [hw, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have hwl : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w := by
    obtain ⟨P, hP, hvP⟩ := hlow
    exact ⟨P, hP, hw1, Submodule.smul_mem _ _ hvP⟩
  have hwK : (R ν).KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hwl
  have hvK : (R ν).KFin v := by
    obtain ⟨S, hS1, hS2, hS3⟩ := hwK
    exact ⟨S, hS1, by rw [hvw]; exact S.smul_mem _ hS2, hS3⟩
  have hws : w ∈ (R ν).sm := hTK _ (hKT _ hwK)
  obtain ⟨v₁, hv₁, hl⟩ := GlobalTheory.T.discrete_series_bessel_gap hH k r _ _ (h / 2) (R ν) Wp z π u μW μN μG νq B (l ν) v hDS hgap hOK hSide hB
    hvK h0 ht hBe
  have hnz : NzOn (R ν) (l ν) := ⟨v₁, hTK _ (hKT _ hv₁), hl⟩
  obtain ⟨c, hc⟩ := GlobalTheory.BesselLine.bessel_line hH k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) B hDS hSide hBe.1 hnz hB
  have hmass := ((GlobalTheory.MomMass.mom_mass hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν).2 hnz).2 w hws
  have hmom := GlobalTheory.T.mass_bound_low_types_sum hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν q h1 h2 w hwl a
  obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hSide
  obtain ⟨m0, m1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 m0 m1 hq
  set K : ℝ := (‖v‖ * ‖c‖) ^ 2 / dg ν with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ᵐ x ∂νq, ‖B ((R ν).σ (Matrix.of x) v)‖ ^ 2 = K * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) := by
    filter_upwards [hae] with x hx
    have hxs := hsm _ hx w hws
    have : B ((R ν).σ (Matrix.of x) v) = ((‖v‖ : ℝ) : ℂ) • c • l ν ((R ν).σ (Matrix.of x) w) := by
      conv_lhs => rw [hvw, map_smul]
      rw [hB.2.1 _ _ hxs, hc _ hxs]
    rw [this, norm_smul, norm_smul, Complex.norm_real, norm_norm, hK]
    field_simp
  have e1 : l2SG νq (fun g => B ((R ν).σ g v)) = ENNReal.ofReal K := by
    rw [hw1, one_pow, ENNReal.ofReal_one] at hmass
    rw [← mul_one (ENNReal.ofReal K), ← hmass, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [sq_nnnorm, hx, one_mul, ENNReal.ofReal_mul hK0]
  rw [e1, mul_comm (ENNReal.ofReal _) (ENNReal.ofReal K)]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right hmom _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hpt] with x hx
  have hl0 : 0 ≤ lenA k r z (Matrix.of x) a ^ (2 * q) := pow_nonneg Metric.infDist_nonneg _
  rw [sq_nnnorm, hx, ← ENNReal.ofReal_mul hl0, ← ENNReal.ofReal_mul hK0]
  congr 1; ring

theorem haar_of_conj {k r : ℕ} {μ : Measure (Mt k r)} {t : MatKR k r} (ht : IsUnit t.det)
    (hN : ∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r)
    (h : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (μ.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j)) :
    PI.BesselPeriodGGP.IsHaarOn (Nset k r) μ := by
  have hc : ∀ g g' : MatKR k r, Continuous fun x : Mt k r => (fun i j => (g * Matrix.of x * g') i j : Mt k r) :=
    fun g g' => ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const :
      Continuous fun x : MatKR k r => g * x * g')
  have hl : ∀ g : MatKR k r, Measurable (lmulM g : Mt k r → Mt k r) := fun g =>
    (show Continuous (lmulM g : Mt k r → Mt k r) from
      (continuous_const.matrix_mul continuous_id : Continuous fun x : MatKR k r => g * x)).measurable
  have i1 : ∀ x : MatKR k r, t * (t⁻¹ * x * t) * t⁻¹ = x := fun x => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left t x ht, Matrix.mul_nonsing_inv_cancel_right t x ht]
  have i2 : ∀ x : MatKR k r, t⁻¹ * (t * x * t⁻¹) * t = x := fun x => by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left t x ht, Matrix.nonsing_inv_mul_cancel_right t x ht]
  let e0 : Mt k r ≃ₜ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j
      invFun := fun x => fun i j => (t * Matrix.of x * t⁻¹) i j
      left_inv := fun x => (i1 (Matrix.of x) :)
      right_inv := fun x => (i2 (Matrix.of x) :)
      continuous_toFun := hc _ _
      continuous_invFun := hc _ _ }
  let e := e0.toMeasurableEquiv
  obtain ⟨h1, h2, h3, h4⟩ : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (μ.map e) := h
  refine ⟨?_, fun h0 => h2 (by rw [h0, Measure.map_zero]), ?_, fun s hs => ?_⟩
  · rw [← e.map_symm_map (μ := μ)]
    exact e.symm.sigmaFinite_map
  · rw [e.map_apply] at h3
    rw [← h3]
    congr 1
    ext x
    have := hN (t⁻¹ * Matrix.of x * t)
    rw [i1] at this
    exact not_congr this.symm
  · have hs' : t⁻¹ * s * t ∈ Nset k r := (hN _).2 (by rwa [i1])
    apply e.map_measurableEquiv_injective
    show (μ.map (lmulM s)).map e = μ.map e
    rw [← h4 _ hs', Measure.map_map e.measurable (hl _), Measure.map_map (hl _) e.measurable]
    congr 1
    funext x
    show t⁻¹ * (s * Matrix.of x) * t = t⁻¹ * s * t * (t⁻¹ * Matrix.of x * t)
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left t _ ht]

theorem size_bound {b v g T x Cg Cu CT : ℝ} {r q : ℕ} (hb : Real.exp 1 < b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b)
    (hg : 1 ≤ g) (hgb : g ≤ b ^ (2 * Cg)) (hCg : 8 ≤ Cg) (hT : T ≤ b ^ (CT * (2 * r + 2 : ℝ))) (hx0 : 0 ≤ x)
    (hx : x ≤ max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ^ r) :
    x ^ (2 * q) * Hsq r T (b ^ max 2 Cu) ^ q ≤
      b ^ (2 * (2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ) * q) := by
  have hb2 : 2 < b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hB : (2 : ℝ) ≤ max 2 Cu := le_max_left _ _
  have hp := Real.pi_gt_three
  have hg2 : 1 ≤ b ^ (2 * Cg) := hg.trans hgb
  have hM : max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ≤ b ^ (2 * Cg + 2) := by
    rw [Real.rpow_add hb0, Real.rpow_two]
    refine max_le ?_ ?_
    · have : Real.pi / v / g ≤ Real.pi :=
        (div_le_self (by positivity) hg).trans (div_le_self (by positivity) hv)
      have := Real.pi_le_four
      nlinarith
    · rw [div_div, inv_div, div_le_iff₀ (by positivity)]
      have h1 : v * g ≤ b ^ 2 * b ^ (2 * Cg) := mul_le_mul (by nlinarith) hgb (by linarith) (by positivity)
      have : 0 ≤ b ^ (2 * Cg) * b ^ 2 := by positivity
      nlinarith
  have h1 : x ≤ b ^ ((2 * Cg + 2) * r) := by
    rw [Real.rpow_mul_natCast hb0.le]
    exact hx.trans (pow_le_pow_left₀ (le_max_of_le_left (by positivity)) hM r)
  have h2 : max 1 T ≤ b ^ (|CT| * (2 * r + 2 : ℝ)) :=
    max_le (Real.one_le_rpow hb1 (by positivity))
      (hT.trans (Real.rpow_le_rpow_of_exponent_le hb1 (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))))
  have h3 : x ^ 2 * Hsq r T (b ^ max 2 Cu) ≤
      b ^ (2 * (2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ)) := by
    unfold Hsq
    calc x ^ 2 * (max 1 T * (b ^ max 2 Cu) ^ (20 * (r + 1)))
        ≤ (b ^ ((2 * Cg + 2) * r)) ^ 2 * (b ^ (|CT| * (2 * r + 2 : ℝ)) * (b ^ max 2 Cu) ^ (20 * (r + 1))) := by
          gcongr
      _ = b ^ ((2 * Cg + 2) * r * (2 : ℕ) + (|CT| * (2 * r + 2 : ℝ) + max 2 Cu * (20 * (r + 1) : ℕ))) := by
          rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_mul_natCast hb0.le _ 2,
            Real.rpow_mul_natCast hb0.le (max 2 Cu)]
      _ ≤ _ := by
          refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
          push_cast
          have := abs_nonneg CT
          nlinarith [mul_nonneg this hr, mul_nonneg (by linarith : 0 ≤ Cg) hr, mul_nonneg (by linarith : 0 ≤ max 2 Cu) hr]
  rw [pow_mul, ← mul_pow, Real.rpow_mul_natCast hb0.le]
  exact pow_le_pow_left₀ (by unfold Hsq; positivity) h3 q

theorem radius_bound {k r m N q : ℕ} {Cn Cq : ℝ} (hm : m = 2 * r + 2) (hk : m ^ 4 ≤ k) (hC : |Cn| + |Cq| ≤ m)
    (hN : (N : ℝ) ≤ Cn * k * (m : ℝ) ^ 3) (hq : (q : ℝ) ≤ Cq * (r : ℝ) ^ 3) :
    N + (r + 1) * q ≤ k * m ^ 5 ∧ (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2 := by
  have a1 := abs_nonneg Cn
  have a2 := abs_nonneg Cq
  have hN' : N ≤ m * k * m ^ 3 := by
    have : (N : ℝ) ≤ m * k * (m : ℝ) ^ 3 := hN.trans (by gcongr; linarith [le_abs_self Cn])
    exact_mod_cast this
  have hq' : q ≤ m * r ^ 3 := by
    have : (q : ℝ) ≤ m * (r : ℝ) ^ 3 := hq.trans (by gcongr; linarith [le_abs_self Cq])
    exact_mod_cast this
  have h1 : (r + 1) * q ≤ m * k :=
    calc (r + 1) * q ≤ m * (m * m ^ 3) :=
          Nat.mul_le_mul (by omega) (hq'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)))
      _ = m * m ^ 4 := by ring
      _ ≤ m * k := Nat.mul_le_mul_left _ hk
  have h2 : m ≤ m ^ 4 := Nat.le_self_pow (by norm_num) m
  constructor
  · calc N + (r + 1) * q ≤ m * k * m ^ 3 + m ^ 4 * k := Nat.add_le_add hN' (h1.trans (Nat.mul_le_mul_right _ h2))
      _ = k * m ^ 4 * 2 := by ring
      _ ≤ k * m ^ 4 * m := Nat.mul_le_mul_left _ (by omega)
      _ = k * m ^ 5 := by ring
  · have : m * k ≤ k * k := Nat.mul_le_mul_right _ (h2.trans hk)
    nlinarith

theorem isBesselMapSm_of {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ}
    {σ : MatKR k r → (H →L[ℂ] H)} {π : MatKR k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (h : IsBesselMapSm (k := k) (r := r) z ψ σ π B) : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  have e : ∀ (w : List (MatKR k r)) (v : H), PI.UpqRep.dsigW (k := k) (r := r) σ w v = dsigW (k := k) (r := r) σ w v := by
    intro w v
    induction w with
    | nil => rfl
    | cons X w ih =>
      show PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ w v) = dsig σ X (dsigW σ w v)
      rw [ih]; rfl
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  exact ⟨h1, h2, h3, C, Ws, h4, fun v hv => by simp only [e]; exact h5 v hv⟩

end GlobalTheory.AmpMoments
