import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPeriodPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.GapCoefficientDerivativeBoundStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapExistsFunctionalStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapsProportionalDiscreteSeriesLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFiniteBesselPeriodNeZeroGapStatement

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpNormalGap

open GlobalTheory.AmpNormal

theorem one_side_gap (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {h : ℝ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ} {c : ℂ}
    {μW μN μG νq : Measure (Mt k r)} {B l : R.H → Wp} {w : R.H} {dd m : ℝ}
    (hdg : R.IsDG ε mu) (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hS : SideG k r z π u μW μN μG νq) (hc : c ≠ 0)
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B)
    (hl : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π l)
    (hbe : ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hw : R.KFin w) (hm : 0 < m)
    (hmass : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) = ENNReal.ofReal m)
    (hd0 : 0 < dd) (hdd : ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) :
    (∃ v, R.KFin v ∧ l v ≠ 0) ∧ ∃ β : ℂ, (∀ v ∈ R.sm, B v = β • l v) ∧ m * dd = ‖β‖ ^ 2 * ‖w‖ ^ 2 := by
  have hds : R.IsDS ε mu := GlobalTheory.isDS_of_isDG hdg
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  obtain ⟨hmul, hone, hinn, hsm, hTKsm, hTK, hKT, -, hcont⟩ := GlobalTheory.rep_basic_of_isDS hKF k r ε mu R hds
  obtain ⟨hG1, hGm, hGi⟩ := uHGroup _ _ (det_hpk k r)
  obtain ⟨t, ht, hN, hz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r c hc
  obtain ⟨-, hcomm, hpsi⟩ := hz z hS.1
  have htd : IsUnit t.det := (hGi t ht).1
  have hti : t⁻¹ ∈ GG k r := (hGi t ht).2
  have hU : Formalism.MainNotions.S.IsURepOn (GG k r) R.σ := by
    refine ⟨⟨ContinuousLinearMap.ext hone, fun a ha b hb => ContinuousLinearMap.ext (hmul a ha b hb)⟩, fun g hg v => ?_,
      hcont⟩
    rw [@norm_eq_sqrt_re_inner ℂ, hinn g hg, ← @norm_eq_sqrt_re_inner ℂ]
  have e1 : ∀ v, R.σ t⁻¹ (R.σ t v) = v := fun v => by
    rw [← hmul _ hti _ ht, Matrix.nonsing_inv_mul _ htd, hone]
  have e2 : ∀ v, R.σ t (R.σ t⁻¹ v) = v := fun v => by
    rw [← hmul _ ht _ hti, Matrix.mul_nonsing_inv _ htd, hone]
  obtain ⟨hS', hR⟩ := GlobalTheory.BesselMoveGap.bessel_move_gap hH k r Wp z π u c μW μN μG νq t ht hN hcomm hpsi hS
  obtain ⟨hbes, hmove⟩ := hR R hU
  obtain ⟨l₁, hl₁⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r ε mu h R Wp z π u μW _ μG _ hdg hgap hok hS'
  have hl₂ : IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) (fun v => l (R.σ t v)) := by
    refine ⟨(hbes l).1 hl, fun x hx v hv => ⟨(hl₁.2 x hx v hv).1, ?_⟩⟩
    rw [(hl₁.2 x hx v hv).2, ← hbe _ (hsm t ht x hx) _ (hTK t ht v hv),
      hmove l₁ hl₁ _ (hsm t ht x hx) _ (hTK t ht v hv), e1, e1]
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r :=
    (GlobalTheory.quotMeas_ae_mem_and_measurable hKF k r ε mu R Wp z π u μW μN μG νq hds hS).1
  have htr : ∀ F : R.H → Wp,
      PI.BesselPeriodGGP.l2SG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) (fun g => F (R.σ t (R.σ g w))) =
        PI.BesselPeriodGGP.l2SG νq (fun g => F (R.σ g w)) := by
    intro F
    unfold PI.BesselPeriodGGP.l2SG
    refine (lintegral_map_equiv _ (lmulEquiv t htd)).trans (lintegral_congr_ae ?_)
    filter_upwards [hae] with x hx
    have : R.σ t (R.σ (Matrix.of (lmulEquiv t htd x)) w) = R.σ (Matrix.of x) w := by
      show R.σ t (R.σ (t⁻¹ * Matrix.of x) w) = _
      rw [hmul _ hti _ hx, e2]
    simp only [this]
  have hB₁ : IsBes R z π (fun v => B (R.σ t v)) := (hbes B).1 hB
  obtain ⟨v, hv, hv0⟩ := GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap hH k r ε mu h R Wp z π u μW _ μG _ (fun v => B (R.σ t v))
    (fun v => l (R.σ t v)) w hds hgap hok hS' hB₁ hw
    (by rw [htr B, hmass]; exact (ENNReal.ofReal_pos.2 hm).ne') (by rw [htr B, hmass]; exact ENNReal.ofReal_ne_top) hl₂
  have hvs : v ∈ R.sm := hTKsm v (hKT v hv)
  have hnz : NzOn R (fun v => l (R.σ t v)) := ⟨v, hvs, hv0⟩
  refine ⟨GlobalTheory.exists_kFin_ne_zero_of_cwCont hKF k r ε mu R hds Wp l hl.1 hl.2.1 hl.2.2.2 ⟨_, hsm t ht v hvs, hv0⟩, ?_⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.T.besselMaps_proportional_discreteSeries_largeGap hH k r ε mu R Wp z π u μW _ μG _ _ _ hdg hS' hl₂.1 hnz hB₁
  have hβ' : ∀ v ∈ R.sm, B v = β • l v := fun v hv => by
    have := hβ _ (hsm _ hti v hv)
    simpa only [e2] using this
  refine ⟨β, hβ', ?_⟩
  have hws : w ∈ R.sm := hTKsm w (hKT w hw)
  have hiso := (Gp91.GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH.1 k r ε mu h R Wp z π u μW _ μG _ _ dd hdg hgap hok hS' hl₂ hdd hnz).2 w hws
  have h2 := (htr fun v => ((Real.sqrt dd : ℝ) : ℂ) • l v).symm.trans hiso
  have h3 : ENNReal.ofReal dd * PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) =
      ENNReal.ofReal (‖β‖ ^ 2) * PI.BesselPeriodGGP.l2SG νq (fun g => ((Real.sqrt dd : ℝ) : ℂ) • l (R.σ g w)) := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    have en : ∀ y : Wp, ((‖y‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := fun y => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]; rfl
    rw [en, en, hβ' _ (hsm _ hx w hws), ← ENNReal.ofReal_mul hd0.le, ← ENNReal.ofReal_mul (by positivity),
      norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow,
      Real.sq_sqrt hd0.le]
    congr 1
    ring
  rw [hmass, h2, ← ENNReal.ofReal_mul hd0.le, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at h3
  linarith

theorem amp_eq_smul_normalised_gap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ) (l : A.H → W.Wp) (l' : A.H → W.Wq), haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; 0 < θ → 0 < D.host.ka / gg D → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → GapAtLeast (epsSH D.R) lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) A.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') A.σ W.π' l' → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π A.σ W.μW W.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z' ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' A.σ W.μW' W.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l v ≠ 0) ∧ (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l' v ≠ 0) ∧ ∃ (w0 : A.H) (η : ℂ), PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 ∧ ‖η‖ = PI.BesselPeriodGGP.fdegH W.μG A.σ w0 * Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧ ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) → ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 → A.J ν γ = η • amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 ν γ := by
  intro hH D τ w w' θ W lam A h l l' hθ hka hT hT' hW hA hgap hok hl hl' hbe hbe'
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW
  obtain ⟨hlam, hds, b1, b2, hsm0, hv0, ⟨P, hP, hlowK⟩, hc, l1, l2, -⟩ := hA
  set R : Rep D.R.k D.R.rS := ⟨A.H, A.σ⟩ with hR
  have hDS : R.IsDS (epsSH D.R) lam := ⟨hlam, hds⟩
  have hDG : R.IsDG (epsSH D.R) lam := ⟨hlam, hds, h, hgap, hok⟩
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  obtain ⟨-, -, -, hsm, hTKsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS hKF _ _ _ _ R hDS
  obtain ⟨-, hGm, -⟩ := uHGroup _ _ (det_hpk D.R.k D.R.rS)
  rw [hN] at q1 q2 hbe hbe'
  obtain ⟨U, hS⟩ := sideG_of ENNReal.ofReal_lt_top z1 (t1 ▸ hT) c1 w1 hG q1
  obtain ⟨U', hS'⟩ := sideG_of ENNReal.ofReal_lt_top z2 (t2 ▸ hT') c2 w2 hG q2
  have hcs : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    have : 2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) = 2 * (D.host.ka / gg D) := by
      rw [mul_div_assoc]; rfl
    rw [this]
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * (D.host.ka / gg D)).ne'
  have hn : 0 < ‖A.v0‖ := norm_pos_iff.2 hv0
  set w0 : A.H := ((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0 with hw0
  have hw1 : ‖w0‖ = 1 := by rw [hw0, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hlow : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 :=
    ⟨P, hP, hw1, Submodule.smul_mem _ _ hlowK⟩
  have hv : A.v0 = ((‖A.v0‖ : ℝ) : ℂ) • w0 := by
    rw [hw0, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have hwK : R.KFin w0 := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  have hvK : R.KFin A.v0 := by
    obtain ⟨S, h1, h2, h3⟩ := hwK
    exact ⟨S, h1, hv ▸ S.smul_mem _ h2, h3⟩
  have hws : w0 ∈ R.sm := hTKsm _ (hKT _ hwK)
  obtain ⟨c₀, hc₀, hdeg⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 _ _ (epsSH D.R) W.μG hG
  have hdd := (hdeg lam R hDG).1
  have hd0 : 0 < c₀ * Formalism.QuantumDeterminants.fdegHC lam := mul_pos hc₀ (GlobalTheory.BesselNorm.fdegHC_pos lam hlam.1.injective)
  set dd := c₀ * Formalism.QuantumDeterminants.fdegHC lam
  have hp : (0 : ℝ) < Module.finrank ℂ W.Wp := by
    obtain ⟨g, -, hnt, -⟩ := c1
    exact_mod_cast Module.finrank_pos
  have hq : (0 : ℝ) < Module.finrank ℂ W.Wq := by
    obtain ⟨g, -, hnt, -⟩ := c2
    exact_mod_cast Module.finrank_pos
  obtain ⟨nz1, β, hβ, e1⟩ := one_side_gap hH R (B := A.B) (l := l) hDG hgap hok hS hcs (isBesselMapSm_of b1) hl hbe hvK
    (mul_pos hc hp) l1 hd0 hdd
  obtain ⟨nz2, β', hβ', e2⟩ := one_side_gap hH R (B := A.B') (l := l') hDG hgap hok hS' hcs (isBesselMapSm_of b2) hl' hbe'
    hvK (mul_pos hc hq) l2 hd0 hdd
  refine ⟨nz1, nz2, w0, (A.cN : ℂ)⁻¹ * ((β * (‖A.v0‖ : ℝ)) * star (β' * (‖A.v0‖ : ℝ))), hlow, ?_, ?_⟩
  · have hw00 : w0 ≠ 0 := by rw [← norm_pos_iff, hw1]; exact one_pos
    rw [show PI.BesselPeriodGGP.fdegH W.μG A.σ w0 = dd from hdd w0 hw00]
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    simp only [norm_mul, norm_star, norm_inv, Complex.norm_real, norm_norm, Real.norm_of_nonneg hc.le]
    have e1' : ‖β‖ ^ 2 * ‖A.v0‖ ^ 2 = A.cN * Module.finrank ℂ W.Wp * dd := e1.symm
    have e2' : ‖β'‖ ^ 2 * ‖A.v0‖ ^ 2 = A.cN * Module.finrank ℂ W.Wq * dd := e2.symm
    rw [mul_pow, mul_pow, mul_pow, mul_pow, e1', e2']
    field_simp
  · intro ν γ hγ hν
    have hae : ∀ᵐ x ∂ν, Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) := hν
    unfold LocS.J amp ampJ
    rw [Complex.ofReal_one, inv_one, one_smul, mul_smul]
    congr 1
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    have a1 : A.Φ (γ * Matrix.of x) = (β * (‖A.v0‖ : ℝ)) • l (A.σ (γ * Matrix.of x) w0) := by
      have hs := hsm _ (hGm _ hγ _ hx) w0 hws
      have hs' := hsm _ (hGm _ hγ _ hx) A.v0 hsm0
      unfold LocS.Φ
      rw [hβ _ hs', mul_smul, ← hl.2.1 _ _ hs, ← map_smul, ← hv]
    have a2 : A.Φ' (Matrix.of x) = (β' * (‖A.v0‖ : ℝ)) • l' (A.σ (Matrix.of x) w0) := by
      have hs := hsm _ hx w0 hws
      have hs' := hsm _ hx A.v0 hsm0
      unfold LocS.Φ'
      rw [hβ' _ hs', mul_smul, ← hl'.2.1 _ _ hs, ← map_smul, ← hv]
    rw [a1, a2]
    ext y
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, ContinuousLinearMap.smul_apply,
      smul_smul]
    congr 1
    simp only [RCLike.star_def]
    ring

end GlobalTheory.AmpNormalGap
