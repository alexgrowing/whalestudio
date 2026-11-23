import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableRootCoords
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudePieriRelevantCellLargeGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumDegreeEqMulFormalDegreeGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqSmulNormalisedAmplitudeLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OpenCellAmplitudeNormEqConstDivDegreeLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqKFiniteOrbitalIntegralGapStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapExistsFunctionalStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpBesselGap

section scale

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants

theorem exists_bessel_scale (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ}
    {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ} {c : ℂ} {μW μN μG νq : Measure (Mt k r)} (hc : c ≠ 0)
    (hS : SideG k r z π u μW μN μG νq) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) (hR : R.IsDG ε mu) (hU : Formalism.MainNotions.S.IsURepOn (GG k r) R.σ) (hg : GapAtLeast ε mu h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) :
    ∃ l : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π l ∧
      ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x) := by
  obtain ⟨t, ht, hN, hz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r c hc
  obtain ⟨-, hW, hψ⟩ := hz z hS.1
  obtain ⟨hS', hm⟩ := GlobalTheory.BesselMoveGap.bessel_move_gap hH k r Wp z π u c μW μN μG νq t ht hN hW hψ hS
  obtain ⟨l₁, hl⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r ε mu h R Wp _ _ _ _ _ _ _ hR hg hok hS'
  obtain ⟨h1, h2⟩ := hm R hU
  refine ⟨fun v => l₁ (R.σ t⁻¹ v), (h1 _).2 ?_, h2 l₁ hl⟩
  have e : (fun v => l₁ (R.σ t⁻¹ (R.σ t v))) = l₁ := by
    funext v
    have h3 := hU.1.2 _ (PI.HwUniqW.inv_mem_UH ht) _ ht
    rw [show t⁻¹ * t = 1 from PI.HwUniqW.inv_mul_UH' ht, hU.1.1] at h3
    exact congrArg l₁ (congrArg (fun T : R.H →L[ℂ] R.H => T v) h3).symm
  show IsBes R z π (fun v => l₁ (R.σ t⁻¹ (R.σ t v)))
  rw [e]
  exact hl.1

end scale

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions in

theorem exists_coef (hH : GlobalTheory.GapIn.Hyp) {Cg cb Cu cT CT C0 Cn : ℝ} (D : D7) (large₂ : SizeData₂ D) {C' Cl : ℝ}
    (hCl : 1000 ≤ Cl) (hm₀ : Cn ≤ D.R.m) (hcd : cdScaleTie D) (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0) τ w w'
    (hTT : HypTT D w w') {θ : ℝ} (hθ : 0 < θ)
    (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (hl : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3) (A : LocS W) (hA : GoodS D lam' A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') :
    0 < A.deg ∧ ∃ f, IsKFinCoefH (toBessel D τ w w' θ W lam' A hW hA hT hT').σ f ∧
      ∀ γ μR νR ν, CellData (toBessel D τ w w' θ W lam' A hW hA hT hT') W.μG γ μR νR ν →
        νR {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 →
        A.J νR γ = OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT') f γ ν := by
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv : 0 < D.host.v := by linarith
  have hka : 0 < D.host.ka := div_pos Real.pi_pos hv
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have hkg : 0 < D.host.ka / gg D := div_pos hka (mul_pos hg0 hg1)
  have hc : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  obtain ⟨hU, -, -, o1, -⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W lam' A hθ hv hTT hW hA
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := o1.2.2.2.2.2.2.2.2.1
  have hW' := hW
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW'
  let sq : (Fin D.R.k → ℝ) → ℕ → ℝ := fun u n => if h : n - 1 < D.R.k then u ⟨n - 1, h⟩ else 0
  have hsq : ∀ u (i : Fin D.R.k), sq u (i.val + 1) = u i := fun u i => by simp [sq]
  have s1 : SideG D.R.k D.R.rS W.z W.π (sq (uS D w τ)) W.μW W.μN W.μG W.νS :=
    ⟨z1, t1 ▸ hT, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z1 (t1 ▸ hT) c1 (hsq _), w1, hNH, hG, q1⟩
  have s2 : SideG D.R.k D.R.rS W.z' W.π' (sq (uS D w' τ)) W.μW' W.μN W.μG W.νS' :=
    ⟨z2, t2 ▸ hT', ⟨_, c2⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z2 (t2 ▸ hT') c2 (hsq _), w2, hNH, hG, q2⟩
  obtain ⟨hNum, hcell, heps⟩ := GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w _ (hsq _)
  obtain ⟨⟨-, -, -, -, hok⟩, hν⟩ := GlobalTheory.NumFam.num_fam _ _ _ _ _ _ _ _ _ hNum
  obtain ⟨ν, hlam, hn1, -⟩ := GlobalTheory.hcParam_sub_integral _ (lamD D τ) lam' hNum.2.1 hA.1
  have hq : n1 ν ≤ D.R.k * D.R.m ^ 5 := by
    have hm : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
    have h1 : Cn ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    have h2 : ((n1 ν : ℕ) : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 5 := by
      rw [hn1]
      calc _ ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := hl
        _ ≤ (D.R.m : ℝ) ^ 2 * D.R.k * (D.R.m : ℝ) ^ 3 := by gcongr
        _ = _ := by ring
    exact_mod_cast h2
  have hgap : GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) := by
    rw [hlam, ← heps]; exact (hν ν hq).2.2.1
  have hDS : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).IsDS (epsSH D.R) lam' := ⟨hA.1, hA.2.1⟩
  have hDG : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).IsDG (epsSH D.R) lam' := ⟨hA.1, hA.2.1, _, hgap, hok⟩
  obtain ⟨l, b1, e1⟩ := exists_bessel_scale hH hc s1 ⟨A.H, A.σ⟩ hDG hU hgap hok
  obtain ⟨l', b2, e2⟩ := exists_bessel_scale hH hc s2 ⟨A.H, A.σ⟩ hDG hU hgap hok
  obtain ⟨⟨v, k1, n1⟩, ⟨v', k2, n2⟩, w0, η, hw0, -, hJ⟩ :=
    GlobalTheory.T.amplitude_eq_smul_normalisedAmplitude_largeGap hH D τ w w' θ W lam' A _ l l' hθ hkg hT hT' hW hA hgap hok b1 b2 e1 e2
  have hw0' : w0 ≠ 0 := by
    obtain ⟨P, -, h1, -⟩ := hw0
    rintro rfl
    simp at h1
  obtain ⟨κ, hκ, hdeg⟩ := GlobalTheory.GapDegreeTie.deg_eq_mul_fdegH hH D τ w w' θ W hcd hW
  obtain ⟨d1, d2⟩ := hdeg lam' A hA ⟨_, hgap, hok⟩ w0 hw0'
  have hfd : 0 < PI.BesselPeriodGGP.fdegH W.μG A.σ w0 := by
    rw [d1] at d2; exact (mul_pos_iff_of_pos_left hκ).1 d2
  have hd : (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hfd.ne'
  rw [hN] at e1 e2
  set d : ℂ := (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) with hd'
  have i1 : ⟪l v, l v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 n1
  have i2 : ⟪l' v', l' v'⟫_ℂ ≠ 0 := inner_self_ne_zero.2 n2
  refine ⟨d2, coefF (toBessel D τ w w' θ W lam' A hW hA hT hT') v v' ((η / (d * (⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ))) • l v)
    (l' v'), GlobalTheory.AmpBessel.isKFinCoefH_coefF (toBessel D τ w w' θ W lam' A hW hA hT hT') k1 k2 _ _, fun γ μR νR ν hD h0 => ?_⟩
  have key := (GlobalTheory.CellPieriG.amp_eq_orb hH (GlobalTheory.T.amplitude_eq_kFiniteOrbitalIntegral_gap hH) GlobalTheory.CellMaj.cellConv (toBessel D τ w w' θ W lam' A hW hA hT hT')
    ⟨A.H, A.σ⟩ lam' _ W.μG l l' w0 hDS hgap hok hcell hc ENNReal.ofReal_ne_top hG e1 e2 hw0 γ μR νR ν hD v v' k1 k2
    ((η / (d * (⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ))) • l v) (l' v')).2
  rw [hJ νR γ hD.1 h0]
  refine Eq.trans ?_ key
  congr 1
  show η = d * (⟪l v, (η / (d * (⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ))) • l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ)
  rw [inner_smul_right]
  field_simp

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Amp in

theorem ampIsBessel : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → D.host.rdE ≤ large₂.sc.b → m₀ ≤ D.R.m → cdScaleTie D → Bridge.AmpIsBessel D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Ca := by
  intro hH Cg cb Cu cT CT C0 C1
  refine ⟨2 * |C1|, by positivity, fun Cn => ?_⟩
  obtain ⟨m₁, hm₁⟩ := GlobalTheory.T.openCellAmplitudeNorm_eq_const_div_degree_largeGap hH (GlobalTheory.T.amplitude_eq_kFiniteOrbitalIntegral_gap hH) GlobalTheory.CellMaj.cellConv Cg cb Cu cT CT C0 C1 Cn
  refine ⟨max Cn m₁, fun D large₂ C' Cl hCl hb hm hcd hZ τ w w' hTT θ hθw W hW lam' hl A hA hT hT' => ?_⟩
  have hb0 : 0 < large₂.sc.b := Real.exp_pos _
  have hθ : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθw.1
  have hm1 : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hb1 : 1 ≤ large₂.sc.b := by
    have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    unfold Host.v at hv1
    linarith
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  obtain ⟨hdpos, f, hf, hJ⟩ := exists_coef hH D large₂ hCl ((le_max_left _ _).trans hm) hcd hZ τ w w' hTT hθ W hW lam' hl A hA hT hT'
  refine ⟨f, 1, one_pos, hf, fun μsec hsec => ?_, fun γ p hp θ' hθ'w νR hν => ?_⟩
  · have e : ThB.jNorm2 (toBessel D τ w w' θ W lam' A hW hA hT hT') f μsec = MMv D w w' A μsec := by
      unfold ThB.jNorm2 jNormSq MMv
      rw [← hW.2.2.2.2.1, ← hW.2.2.2.2.2.1]
      refine lintegral_congr_ae ?_
      filter_upwards [GlobalTheory.AmpBessel.ae_cellData hk (toBessel D τ w w' θ W lam' A hW hA hT hT') W.μG hsec] with q hq
      rcases hq with hq | hq
      · have hq' : bcWeight _ _ (Tz _ _ W.z) (Tz _ _ W.z') q = 0 := hq
        rw [hq, hq', zero_mul, zero_mul]
      · rw [hJ _ _ _ _ hq hG.2.2.1, Real.norm_of_nonneg (Real.sqrt_nonneg _),
          Real.sq_sqrt (GlobalTheory.AmpBessel.hs_nonneg _)]
        rfl
    obtain ⟨K, hK, hM⟩ := hm₁ D large₂ C' Cl hCl ⟨hb, by nlinarith, (le_max_right _ _).trans hm⟩ hcd hZ τ w w' hTT θ hθw W hW
      μsec hsec
    rw [e, ENNReal.ofReal_one, one_mul, hM lam' hl A hA]
    exact ⟨(ENNReal.ofReal_pos.2 (div_pos hK hdpos)).ne', le_rfl⟩
  · have hθ' : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'w.1
    obtain ⟨g, μR, ν₀, ν, s, hD, h0, hrep, hroot, hs, hA'⟩ := GlobalTheory.AmpBessel.amp_at_root D τ w w' θ W hW lam' A hA hT hT' hp hθ' hν
    have hle : ENNReal.ofReal (hsNormSq (OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT') f g (ENNReal.ofReal θ' • ν))) ≤
        Bridge.orbSqO (toBessel D τ w w' θ W lam' A hW hA hT hT') f p :=
      le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le _
        (le_iSup_of_le ⟨hrep, hD.2.2.2.1, hroot, GlobalTheory.AmpBessel.isOrbQuot_smul hD.2.2.2.2.2.1⟩ le_rfl)))
    have e : OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT') f g (ENNReal.ofReal θ' • ν) =
        (θ' : ℂ) • OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT') f g ν := by
      unfold OrbInt
      rw [integral_smul_measure, ENNReal.toReal_ofReal hθ'.le, Complex.coe_smul]
    refine le_trans ?_ (mul_le_mul_right hle _)
    rw [hA', GlobalTheory.AmpNorm.hsNormSq_smul, hJ _ _ _ _ hD h0, e, GlobalTheory.AmpNorm.hsNormSq_smul, hs,
      ← ENNReal.ofReal_mul (by positivity), Complex.norm_real, Real.norm_of_nonneg hθ'.le, one_mul, ← mul_assoc]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (GlobalTheory.AmpBessel.hs_nonneg _))
    have h1 : 1 ≤ large₂.sc.b ^ (|C1| * (D.R.m : ℝ) ^ 2) * θ' := by
      calc (1 : ℝ) ≤ large₂.sc.b ^ (|C1| * (D.R.m : ℝ) ^ 2 + -(C1 * (D.R.m : ℝ) ^ 2)) :=
            Real.one_le_rpow hb1 (by nlinarith [le_abs_self C1, sq_nonneg (D.R.m : ℝ)])
        _ ≤ _ := by
            rw [Real.rpow_add hb0]
            exact mul_le_mul_of_nonneg_left hθ'w.1 (by positivity)
    rw [show 2 * |C1| * (D.R.m : ℝ) ^ 2 = |C1| * (D.R.m : ℝ) ^ 2 * (2 : ℕ) by push_cast; ring, Real.rpow_mul_natCast hb0.le,
      ← mul_pow]
    exact pow_le_pow_left₀ zero_le_one h1 2

end GlobalTheory.AmpBesselGap

end
