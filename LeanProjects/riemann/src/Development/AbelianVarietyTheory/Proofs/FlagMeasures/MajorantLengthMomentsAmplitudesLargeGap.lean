import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTranslate
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupBesselGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapsProportionalDiscreteSeriesLargeGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLocalDataMomentPieriHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneMajorantLengthMomentLowestKTypeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFiniteBesselPeriodNeZeroGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypothesesStatement

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.AmpMomentsGap

theorem family_through_at_gap (hH : GlobalTheory.GapIn.Hyp) (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b bv ga h : ℝ) (q0 : ℕ) (ν₀ : Fin (2 * r + k + 1) → ℤ) (R0 : Rep k r) (hN : Num k r lam u b bv ga h q0)
    (hR0 : R0.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν₀ a : ℝ))) :
    ∃ R : (Fin (2 * r + k + 1) → ℤ) → Rep k r, IsFam lam q0 R ∧ R ν₀ = R0 := by
  classical
  have hex : DSExistG := hH.1.2.2.2.1
  have hC : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P := by
    obtain ⟨P, hP, -⟩ := hR0.2
    exact ⟨P, hP⟩
  have H := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  have key : ∀ ν : Fin (2 * r + k + 1) → ℤ, ∃ R : Rep k r,
      (∑ a, (ν a).natAbs ≤ q0 → R.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))) ∧
      (ν = ν₀ → R = R0) := by
    intro ν
    by_cases h0 : ν = ν₀
    · refine ⟨R0, fun _ => ?_, fun _ => rfl⟩
      subst h0
      exact hR0
    · by_cases hq : ∑ a, (ν a).natAbs ≤ q0
      · obtain ⟨R, hR⟩ := hex k r _ _ (H.2 ν hq).1 hC ⟨h / 2, (H.2 ν hq).2.2.1, H.1.2.2.2.2⟩
        exact ⟨R, fun _ => GlobalTheory.isDS_of_isDG hR, fun h => absurd h h0⟩
      · exact ⟨R0, fun h => absurd h hq, fun _ => rfl⟩
  choose R hR using key
  exact ⟨R, fun ν hν => (hR ν).1 hν, (hR ν₀).2 rfl⟩

theorem moment_of_bessel (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
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
  obtain ⟨-, -, -, hsm, hTK, -, hKT, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 k r _ _ (R ν) hDS
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
  obtain ⟨v₁, hv₁, hl⟩ := GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap hH k r _ _ (h / 2) (R ν) Wp z π u μW μN μG νq B (l ν) v hDS hgap hOK hSide hB
    hvK h0 ht hBe
  have hnz : NzOn (R ν) (l ν) := ⟨v₁, hTK _ (hKT _ hv₁), hl⟩
  have hDG : (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) := ⟨hDS.1, hDS.2, ⟨h / 2, hgap, hOK⟩⟩
  obtain ⟨c, hc⟩ := GlobalTheory.GapLine.bessel_line_gap hH k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) B hDG hSide hBe.1 hnz hB
  have hmass := ((Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg
    ((GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg).1 hS) ν hν).2 hnz).2 w hws
  have hmom := GlobalTheory.T.oneMajorantLength_moment_lowestKType hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν q h1 h2 w hwl a
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
    rw [GlobalTheory.AmpMoments.sq_nnnorm, hx, one_mul, ENNReal.ofReal_mul hK0]
  rw [e1, mul_comm (ENNReal.ofReal _) (ENNReal.ofReal K)]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right hmom _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hpt] with x hx
  have hl0 : 0 ≤ lenA k r z (Matrix.of x) a ^ (2 * q) := pow_nonneg Metric.infDist_nonneg _
  rw [GlobalTheory.AmpMoments.sq_nnnorm, hx, ← ENNReal.ofReal_mul hl0, ← ENNReal.ofReal_mul hK0]
  congr 1; ring

theorem amplitude_moments_gap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 C1 Cq : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C := by
  intro hH Cg cb Cu cT CT C0 C1 Cq
  refine ⟨2 * Cg + 2 + |CT| + 10 * max 2 Cu, fun Cn => ⟨|Cn| + |Cq|, ?_⟩⟩
  intro D large₂ C' Cl hCl hBig hZ τ w w' hTT θ _ W hW lam' hlam A hA a q hq
  haveI := FiniteDimensional.complete ℂ W.Wp
  obtain ⟨-, -, hb, hm, -, -, -, hmk, hv, -, hka, hvb, hg, hgb, hCg, -, hT, -⟩ :=
    GlobalTheory.Amp.RangeModel.sizes_of D large₂ C' Cl Cg cb Cu cT CT C0 hBig.1 hZ
  have hθ := GlobalTheory.Amp.RangeModel.theta_pos D τ w w' θ W hW
  obtain ⟨hNum, -, heps⟩ := GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w (uOne D w τ) (fun i => by
    have := i.isLt
    simp only [uOne]
    rw [dif_pos ⟨by omega, by omega⟩]; rfl)

  have hex : ∀ i, ∃ n : ℤ, lam' i = lamD D τ i + n := fun i => by
    obtain ⟨n₁, h₁⟩ := hA.1.2 i
    obtain ⟨n₂, h₂⟩ := hNum.2.1.2 i
    exact ⟨n₁ - n₂, by push_cast at *; linarith⟩
  choose ν hν using hex
  obtain rfl : lam' = fun i => lamD D τ i + (ν i : ℝ) := funext hν
  have hn1 : ((n1 ν : ℕ) : ℝ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := by
    refine le_trans (le_of_eq ?_) hlam
    simp [n1, l1dist]
  obtain ⟨hr1, hr2⟩ := GlobalTheory.AmpMoments.radius_bound hm hmk hBig.2.2 hn1 hq
  let R0 : Rep D.R.k D.R.rS := { H := A.H, σ := A.σ }
  obtain ⟨hA1, hA2, hA3, -, hA5, hA6, hA7, hA8, hA9, -⟩ := hA
  rw [← heps] at hA2 hA7
  have hDS : R0.IsDS (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) (fun i => lamD D τ i + (ν i : ℝ)) := ⟨hA1, hA2⟩
  obtain ⟨R, hFam, hR⟩ := family_through_at_gap hH _ _ _ _ _ _ _ _ _ ν R0 hNum hDS

  set c : ℝ := 2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) with hc
  have hc2 : c = 2 * (Real.pi / D.host.v / gg D) := by rw [hc, hka, gg]; ring
  have hc0 : 0 < c := by rw [hc2]; have := Real.pi_pos; positivity
  obtain ⟨t, htG, htN, htz, hts⟩ := GlobalTheory.T.exists_unitaryTorus_scale_besselCharacter D.R.k D.R.rS (c : ℂ) (by exact_mod_cast hc0.ne')
  choose s hs0 hs1 hs2 hs3 using hts
  have htd : IsUnit t.det := Matrix.isUnit_det_of_right_inverse (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv htG).2.1
  obtain ⟨U, U', l, l', dg, hS, -⟩ := GlobalTheory.T.amplitudeLocalData_momentPieriHypotheses hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w' θ W hTT hθ hW t htG
    htN (fun z hz => (htz z hz).2) R hFam
  obtain ⟨-, -, hz, -, hTz, -, hG, -, -, -, -, -, hQ, -⟩ := hW
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hS.2.2.1
  have hSide : SideG D.R.k D.R.rS W.z W.π U W.μW W.μN W.μG W.νS :=
    ⟨g1, g2, g3, g4, g5, GlobalTheory.AmpMoments.haar_of_conj htd htN g6, g7, hQ⟩
  have hB := (((GlobalTheory.BesselMoveGap.bessel_move_gap hH _ _ W.Wp W.z W.π U (c : ℂ) W.μW W.μN W.μG W.νS t htG htN (htz _ hz).2.1
    (htz _ hz).2.2 hSide).2 R0 (GlobalTheory.TensCompare.isURepOn_of_isDS hDS)).1 A.B).1 (GlobalTheory.AmpMoments.isBesselMapSm_of hA3)
  obtain ⟨hmul, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 _ _ _ _ R0 hDS
  obtain ⟨m0, m1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts g5 g6
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot g7.2.2.1 m0 m1 g8
  set νq := W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j with hνq
  have hpt : ∀ᵐ x ∂νq, A.Φ (t * Matrix.of x) = A.B (R0.σ t (R0.σ (Matrix.of x) A.v0)) := by
    filter_upwards [hae] with x hx
    exact congrArg A.B (hmul t htG _ hx A.v0)
  have e1 : l2SG W.νS A.Φ = l2SG νq (fun g => A.B (R0.σ t (R0.σ g A.v0))) := by
    unfold l2SG
    rw [GlobalTheory.AmpMoments.lintegral_translate W.νS t htd]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [← hx]; rfl
  have hfr : 0 < Module.finrank ℂ W.Wp := by
    obtain ⟨_, _, -, hρ⟩ := g3
    haveI := hρ.1
    exact Module.finrank_pos
  have key := moment_of_bessel hH hS ν q hr1 hr2 R0 hR _ hB A.v0 hA6 hA7
    (by rw [← e1, hA9]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne')
    (by rw [← e1, hA9]; exact ENNReal.ofReal_ne_top) a
  have hsz := GlobalTheory.AmpMoments.size_bound (q := q) (Cu := Cu) hb hv hvb hg hgb hCg (T := Tz D.R.k D.R.rS W.z) (CT := CT)
    (r := D.R.rS) (by rw [hTz]; have := hT w; rw [hm] at this; exact_mod_cast this) (norm_nonneg (s a)) (by
      have := hs1 a
      rw [Complex.norm_real, Real.norm_of_nonneg hc0.le, ← inv_div c 2, hc2,
        mul_div_cancel_left₀ _ (two_ne_zero (α := ℝ))] at this
      exact this)
  have hm' : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by rw [hm]; push_cast; ring
  rw [e1, hm']
  refine le_trans ?_ (mul_le_mul_left (ENNReal.ofReal_le_ofReal hsz) _)
  rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right key _)
  rw [GlobalTheory.AmpMoments.lintegral_translate W.νS t htd, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hpt] with x hx
  rw [← hx, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
    ← GlobalTheory.AmpMoments.lenA_mul W.z t (Matrix.of x) s hs0 (fun b => hs3 b _ hz), BranchingSupport.TensInh.lenA_eq_lA]
  rfl

end GlobalTheory.AmpMomentsGap
