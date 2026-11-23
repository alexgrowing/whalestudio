import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingUniformConstantStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapExistsFunctional
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CellDataExists
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentUpperFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapExistsFunctional
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSides
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTorusElementProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueRootCoordinatesMapBesselTorusConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionEqScalarSqNormalisedBesselTorusCon
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadicalStatement

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpNormGap

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P GlobalTheory.AmpNorm

theorem lintegral_hsNormSq_amp_gap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ (k r : ℕ) (L : LocBessel k r) (μG : Measure (Mt k r)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 2 ≤ k → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsSection k r L.z L.z' μsec → ∃ c : ℝ, 0 < c ∧ ∀ (R : Rep k r) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * hsNormSq (amp R l l' w μG (bigCell k r q.1 (μsec q.2)))) = ENNReal.ofReal (c / PI.BesselPeriodGGP.fdegH μG R.σ w ^ 3) := by
  intro hH hAmp hConv k r L μG μsec hk hc hκ0 hκt hG hsec
  have := FiniteDimensional.complete ℂ L.Wp
  have := FiniteDimensional.complete ℂ L.Wq
  have hK : PI.KFinSmooth := hH.1.1.2.2.1
  have hk1 : 1 ≤ k := by omega
  have hstd : cStd ≠ 0 := by simp [cStd]
  have hα : cStd / L.c ≠ 0 := div_ne_zero hstd hc
  have hcα : L.c * (cStd / L.c) = cStd := mul_div_cancel₀ _ hc
  set α := cStd / L.c
  obtain ⟨ha, hT, -, hcell⟩ := ThA.TorusElt.torusElt k r α hα
  have hn : 0 < ‖α‖ := norm_pos_iff.2 hα
  have hGB := (HaarNotions.isHaarOn_iff_groups k r μG).1.1 hG
  have hNB : B.IsHaarOn (Nset k r) L.μN := (HaarNotions.isHaarOn_iff_groups k r L.μN).2.1.1
    (GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r L.κN (pos_iff_ne_zero.2 hκ0) hκt.lt_top)
  have hW := ((HaarNotions.isHaarOn_iff_groups k r L.μW).2.2 L.z L.hz.1 L.hz.2 hk1).1 L.hμW.1
  have hW' := ((HaarNotions.isHaarOn_iff_groups k r L.μW').2.2 L.z' L.hz'.1 L.hz'.2 hk1).1 L.hμW'.1
  have hδ : 0 < ‖α‖ ^ B.kap k r := by positivity
  have hN₁ := haar_smul hNB hδ
  set μ₁ := ENNReal.ofReal (‖α‖ ^ B.kap k r) • L.μN with hμ₁
  have hmap : μ₁.map (conjM (ThA.aT k r α)) = L.μN := by
    rw [ThA.TorusJac.haar_map_conj _ hN₁ α hα, hμ₁, smul_smul, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hδ.ne', ENNReal.ofReal_one, one_smul]
  set a := ThA.aT k r α
  have hu := WeylGroupFacts.isUnit_of_uh ha
  have hai := WeylGroupFacts.uh_inv ha
  have hp : ∀ z, inWb k r z → ∀ n ∈ Nset k r, psi k r z L.c (a * n * a⁻¹) = psi k r z cStd n := by
    intro z hz n hn
    unfold psi
    rw [((hT z hz).2 n hn).2.2, ← mul_assoc L.c, hcα]
  obtain ⟨u, hw⟩ := CapelliOfHC.exists_isType k r L.Wp L.z L.π L.u L.hz.1 L.hz.2 L.hπ
  obtain ⟨u', hw'⟩ := CapelliOfHC.exists_isType k r L.Wq L.z' L.π' L.u' L.hz'.1 L.hz'.2 L.hπ'
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := character_exists_alt
  let D : B.RealPlaceData k r L.Wp L.Wq :=
    ⟨L.z, L.z', L.π, L.π', μG, L.μW, μ₁, L.μW', μsec, χ, hk1, L.hz.1, L.hz'.1, L.hz.2, L.hz'.2,
      hw.2.1, hw'.2.1, hw.2.2.2.1, hw'.2.2.2.1, hw.2.2.1, hw'.2.2.1, hGB, hW, hN₁, hW', hsec, hχ1, hχ2, hχ3⟩
  obtain ⟨ν₁, ν₁', hS, hS'⟩ := exists_sideG_both_of_isType k r L.Wp L.Wq D u u' hw hw'
  obtain ⟨c₀, hc₀, hP⟩ := Gp91.GlobalTheory.T.bessel_setting_uniform_constant hH.1 k r L.Wp L.Wq D
  obtain ⟨c₁, -, hdeg⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 k r L.ε μG hG
  refine ⟨((‖α‖ ^ 2) ^ B.kap k r)⁻¹ * c₀, by positivity, ?_⟩
  intro R mu h l l' w hR hgap hok hgc hl hl' ⟨v, hv, hv0⟩ ⟨v', hv', hv0'⟩ hlow
  have hRG : R.IsDG L.ε mu := ⟨hR.1, hR.2, ⟨h, hgap, hok⟩⟩
  obtain ⟨hmul, h1, hun, hsm, hTK, hTT, hKT, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r L.ε mu R hR
  have hwK : R.KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  have hw0 : w ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hlow
    intro h0
    simp [h0] at hn1
  have hDD : ∀ x ∈ ThreeDimData.DDsp R.σ w, x ∈ R.TK := fun x hx =>
    (Submodule.span_le.2 (by rintro _ ⟨g, hg, rfl⟩; exact hTT g hg w (hKT w hwK)) : ThreeDimData.DDsp R.σ w ≤ R.TK) hx
  set d := PI.BesselPeriodGGP.fdegH μG R.σ w with hd
  have hdd : ∀ x, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ x = d := fun x hx => by
    rw [hd, (hdeg mu R hRG).1 x hx, (hdeg mu R hRG).1 w hw0]
  have hd0 : 0 ≤ d := div_nonneg (by positivity) (integral_nonneg fun _ => by positivity)
  obtain ⟨l₁, hl₁⟩ := Gp91.CompanionTheory.FamilyDerivativeExpansion.BeL.exists_normalised_bessel_map hH.1 k r L.ε mu h R L.Wp _ _ _ _ _ _ _ hRG hgap hok hS
  obtain ⟨l₁', hl₁'⟩ := Gp91.CompanionTheory.FamilyDerivativeExpansion.BeL.exists_normalised_bessel_map hH.1 k r L.ε mu h R L.Wq _ _ _ _ _ _ _ hRG hgap hok hS'
  have hy := hTT _ hai _ (hKT v hv)
  have hy' := hTT _ hai _ (hKT v' hv')
  have e₁ : ‖⟪l₁ (R.σ a⁻¹ v), l v⟫_ℂ‖ = ‖⟪l v, l v⟫_ℂ‖ := by
    refine norm_inner_of_rankOne ?_
    rw [← (hl₁.2 _ (hTK _ hy) _ hy).2, ← hl v (hTK _ (hKT v hv)) v (hKT v hv), ← hmap]
    exact (be_conj R hmul h1 hun L.π hW hN₁ ha (hT _ L.hz.1).1 (hp _ L.hz.1) v v).symm
  have e₂ : ‖⟪l₁' (R.σ a⁻¹ v'), l' v'⟫_ℂ‖ = ‖⟪l' v', l' v'⟫_ℂ‖ := by
    refine norm_inner_of_rankOne ?_
    rw [← (hl₁'.2 _ (hTK _ hy') _ hy').2, ← hl' v' (hTK _ (hKT v' hv')) v' (hKT v' hv'), ← hmap]
    exact (be_conj R hmul h1 hun L.π' hW' hN₁ ha (hT _ L.hz'.1).1 (hp _ L.hz'.1) v' v').symm
  let LR : LocBessel k r :=
    { L with lam := mu, hlam := hR.1, Hs := R.H, hsN := R.nacg, hsI := R.ips, hsC := R.cs, σ := R.σ, hσ := hR.2 }
  have hone : OnePlaceKF LR h μG w l l' :=
    ⟨⟨hgap, hok, hc, hlow, hG, fun x hx y hy => hl x (hTK _ (hDD x hx)) y (hDD y hy),
      fun x hx y hy => hl' x (hTK _ (hDD x hx)) y (hDD y hy)⟩,
      fun x hx y hy => hl x (hTK _ (hDD x hx)) y (hKT y hy), fun x hx y hy => hl' x (hTK _ (hDD x hx)) y (hKT y hy)⟩
  let F : B.Mat k r → (L.Wq →L[ℂ] L.Wp) := fun x => coefF LR v v' (l v) (l' v') (a * x * a⁻¹)
  have hF : IsCoef R l₁ l₁' F (⟪l' v', l₁' (R.σ a⁻¹ v')⟫_ℂ * ⟪l₁ (R.σ a⁻¹ v), l v⟫_ℂ) := by
    refine ⟨1, fun _ => R.σ a⁻¹ v, fun _ => R.σ a⁻¹ v', fun _ => (innerSL ℂ (l' v')).smulRight (l v),
      fun _ => ⟨hy, hy'⟩, fun g hg => ?_, ?_⟩
    · rw [Fin.sum_univ_one, ← hun a ha (R.σ a⁻¹ v), ← hmul _ ha _ hai, Matrix.mul_nonsing_inv _ hu, h1,
        ← hmul _ hg _ hai, ← hmul _ ha _ (WeylGroupFacts.uh_mul hg hai), ← Matrix.mul_assoc]
      ext x
      show ⟪l' v', x⟫_ℂ • ⟪v, R.σ (a * g * a⁻¹) v'⟫_ℂ • l v = ⟪v, R.σ (a * g * a⁻¹) v'⟫_ℂ • ⟪l' v', x⟫_ℂ • l v
      exact smul_comm _ _ _
    · rw [Fin.sum_univ_one, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right]
  have hnorm := hP L.ε mu h R l₁ l₁' d hRG hgap hok hl₁ hl₁' hdd F _ hF
  set S : ℂ := ⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ with hSdef
  have hS0 : 0 < ‖S‖ := norm_pos_iff.2 (mul_ne_zero (inner_self_ne_zero.2 hv0) (inner_self_ne_zero.2 hv0'))
  rw [norm_mul, norm_inner_symm, e₁, e₂, mul_comm ‖_‖, ← norm_mul, ← hSdef] at hnorm
  have := B7.sf hW
  have := B7.sf hW'
  have := B7.sf hN₁
  have hpt : ∀ q ∈ B7.Q0 D, hsNormSq (amp R l l' w μG (bigCell k r q.1 (μsec q.2))) =
      (d⁻¹ / ‖S‖) ^ 2 * ‖B.hsVec (B.JF D F (B.gq D (B7.d_S r (‖α‖ ^ 2) q)))‖ ^ 2 := by
    intro q hq
    have hcd := cellData_bigCell LR μG D rfl rfl hq
    obtain ⟨b, hb0, hb1, hb2⟩ := hConv k r LR h μG _ _ _ _ hκt hok hgc hcd hcd.2.2.1
    have hA : S • amp R l l' w μG (bigCell k r q.1 (μsec q.2)) = (d : ℂ)⁻¹ •
        besselJ k r L.z L.z' L.c L.π L.π' L.μW L.μN L.μW' (coefF LR v v' (l v) (l' v'))
          (bigCell k r q.1 (μsec q.2)) :=
      hAmp k r LR h μG w l l' hone _ _ _ _ hcd b hb0 hb1 hb2 v v' hv hv' (l v) (l' v')
    rw [← hmap, ThA.besselJ_conj k r L.z L.z' L.c cStd L.π L.π' L.μW μ₁ L.μW' hW.conc hN₁.conc hW'.conc a hu
      (hT _ L.hz.1).1 (hT _ L.hz'.1).1 (hp _ L.hz.1) (hp _ L.hz'.1), hcell] at hA
    have h2 := congrArg hsNormSq hA
    rw [GlobalTheory.AmpNorm.hsNormSq_smul, GlobalTheory.AmpNorm.hsNormSq_smul, GlobalTheory.AmpNorm.hsNormSq_eq (besselJ _ _ _ _ _ _ _ _ _ _ _ _), norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hd0] at h2
    have e : B.gq D (B7.d_S r (‖α‖ ^ 2) q) =
        bigCell k r (fun i => ((‖α‖ ^ (2 * (r - i.val)) : ℝ) : ℂ) * q.1 i) (μsec q.2) := by
      simp only [pow_mul]
      rfl
    rw [e, div_pow, div_mul_eq_mul_div, eq_div_iff (by positivity), mul_comm]
    exact h2
  rw [lintegral_congr_ae (g := fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal ((d⁻¹ / ‖S‖) ^ 2) *
      ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') q *
        (fun q => ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) (B7.d_S r (‖α‖ ^ 2) q))),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_weight_scale (Tz k r L.z) (Tz k r L.z') (‖α‖ ^ 2) (by positivity)
      (fun q => ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2)]
  · refine (congrArg (fun t => _ * (_ * t)) hnorm).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rcases hd0.eq_or_lt with h0 | h0
    · simp [← h0]
    · field_simp
  · filter_upwards [B7.ae_mem_good_set_or_weight_zero D] with q hQ
    rw [← ENNReal.ofReal_mul (by positivity)]
    rcases hQ with hQ | hQ
    · rw [hpt q hQ, mul_left_comm]
    · have hQ' : bcWeight k r (Tz k r L.z) (Tz k r L.z') q = 0 := hQ
      simp only [hQ', zero_mul, mul_zero]

end GlobalTheory.AmpNormGap
