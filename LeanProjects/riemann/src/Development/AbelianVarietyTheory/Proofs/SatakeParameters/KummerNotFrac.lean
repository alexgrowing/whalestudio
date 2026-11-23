import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedShiftFixedRatioConstDomainStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitOfStableLineStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClosEqZeroOfMulMemStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerPEqSpanBetaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FilPEqSpanBetaDPowStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AinfAdjoinBetaImageDivBetaPowStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaImageDeRhamPlusDvdOfLAdicResiduesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivPowerEnvelopeMemAinfAdjoinBetaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AcrisMemBetaAdicClosureAinfAdjoinBetaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogPeriodCongruenceBdrStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLogOnePlusKerThetaDeRhamPlusStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisLogTeichmullerRatioEqAddKummerStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsKummerFracCoboundaryFullGaloisStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst

theorem StLat.not_frac (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l)
    (hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l)) (u : Per.BdRp l) (hu : IsLogP (beta ϖ) u) (x y : Per.Bcris l)
    (hx : Co.ι x ≠ 0) : Co.ι y ≠ Co.ι x * algebraMap (Per.BdRp l) (Per.BdR l) u := by
  intro h
  obtain ⟨hdom, hdvr, hmax, hmaxθ, -, hfilt, hfr⟩ := BdRDVR.core_dvr l Co
  have hker := GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ
  have hfil := GlobalTheory.T.filP_eq_span_betaD_pow_of_kerP_eq_span_beta l Co ϖ hker
  have hinjD : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
  have hβ0 : betaD ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field (Per.BdRp l)
    rw [hmax, ← pow_one (Co.j Co.t), ← hfilt 1, hfil 1, h0, pow_one, Ideal.span_singleton_eq_bot]
  have hsep : ∀ z : Per.BdRp l, (∀ n : ℕ, betaD ϖ ^ n ∣ z) → z = 0 := by
    intro z hz
    have hne : Ideal.span {betaD ϖ} ≠ ⊤ := by
      rw [← pow_one (betaD ϖ), ← hfil 1, hfilt 1, pow_one, ← hmax]
      exact (IsLocalRing.maximalIdeal.isMaximal (Per.BdRp l)).ne_top
    have h1 : z ∈ ⨅ n : ℕ, Ideal.span {betaD ϖ} ^ n := by
      refine (Submodule.mem_iInf _).2 fun n => ?_
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton.2 (hz n)
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain _ hne, Ideal.mem_bot] at h1
  obtain ⟨r, ax, hax⟩ := bcris_eq_acris_localization_periodT_alt l Co x
  obtain ⟨r', ay, hay⟩ := bcris_eq_acris_localization_periodT_alt l Co y
  set tt := algebraMap (Per.Acris l) (Per.Bcris l) Co.t with htt
  have e1 : algebraMap (Per.Acris l) (Per.Bcris l) (ax * Co.t ^ r') = x * tt ^ (r + r') := by
    rw [map_mul, map_pow, ← hax, pow_add]; ring
  have e2 : algebraMap (Per.Acris l) (Per.Bcris l) (ay * Co.t ^ r) = y * tt ^ (r + r') := by
    rw [map_mul, map_pow, ← hay, pow_add]; ring
  have e3 : Co.j (ay * Co.t ^ r) = Co.j (ax * Co.t ^ r') * u := by
    apply hinjD
    rw [map_mul (algebraMap (Per.BdRp l) (Per.BdR l)), ← Co.ι_j, ← Co.ι_j, e1, e2, map_mul Co.ι, map_mul Co.ι, h]
    ring
  have hA := GlobalTheory.T.acris_mem_betaAdicClosure_ainfAdjoinBeta l Co.j Co.j_cris ϖ (GlobalTheory.T.divPowerEnvelope_mem_ainfAdjoinBeta l ϖ hϖ) hfil
  have hz := GlobalTheory.T.eq_zero_of_mem_clos_of_pow_mul_mul_mem_clos l (Fact.out : l.Prime) (isUnit_l_BdRp l) (betaD ϖ) hβ0 hsep (Sg ϖ)
    (GlobalTheory.T.ainfAdjoinBetaImage_div_beta_pow l ϖ hϖ hker hfil) (GlobalTheory.T.betaImageDeRhamPlus_dvd_of_lAdic_residues l ϖ hker hfil) u
    (GlobalTheory.T.log_period_congruence_bdr l ϖ hker hfil u hu) (Co.j (ax * Co.t ^ r')) 0 (hA _) (by
      rw [pow_zero, one_mul, ← e3]; exact hA _)
  have hz2 : Co.ι (x * tt ^ (r + r')) = 0 := by
    rw [← e1, Co.ι_j, hz, map_zero]
  have htne : Co.ι tt ≠ 0 := by
    rw [htt, Co.ι_j]
    intro h0
    have h3 : Co.j Co.t = 0 := hinjD (h0.trans (map_zero _).symm)
    apply IsDiscreteValuationRing.not_a_field (Per.BdRp l)
    rw [hmax, h3, Ideal.span_singleton_eq_bot]
  haveI : IsDomain (Per.BdR l) := IsFractionRing.isDomain (Per.BdRp l)
  rw [map_mul, map_pow] at hz2
  exact mul_ne_zero hx (pow_ne_zero _ htne) hz2

theorem StLat.kummer_not_frac : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
  ¬ ∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P AI T K b b' hb h
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  obtain ⟨x, y, hx, hxy⟩ := GlobalTheory.T.exists_kummerFracCoboundary_full_galois l P K b b' hb h
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨ϖ, hr⟩ := exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_logOnePlus_kerTheta_deRhamPlus l (beta ϖ) (by
    rw [GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ]; exact Ideal.mem_span_singleton_self _)
  have hg := GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer l P Co hC.ζ ϖ hr hϖ u hu
  letI : Field P.R.BdR := (GlobalTheory.RegularRing.isField_of_tied T).toField
  set U := T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) u) with hUdef
  have hct : ∀ g : GQ l, T.eD (P.ιB ((kummer P g : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l)
        (Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t)) := by
    intro g
    rw [hC.ι, Algebra.smul_def, map_mul, T.zB, hC.t, ← Co.ι_j]
    simp only [Core.tB, GlobalTheory.RingIface.zB_alg, map_mul]
  have hU : ∀ g : GQ l, P.actQdR g U = U + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
    intro g
    apply T.eD.injective
    rw [T.actD, hUdef, RingEquiv.apply_symm_apply, map_add, RingEquiv.apply_symm_apply, hct]
    rw [show Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) u) =
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g u) from
        GlobalTheory.RingIface.sigD_alg l g u, hg, map_add]
  have hcomm : ∀ (g : GQ l) (z : P.R.B), P.ιB (P.actQ g z) = P.actQdR g (P.ιB z) := by
    intro g z
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z
    rwa [P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR] at this
  have hX : P.ιB x ≠ 0 := fun h0 => hx ((P.PD (botExt l)).ι_inj (by rw [P.PD_ι, h0, map_zero]))
  have hgX : ∀ g : GQ l, P.actQdR g (P.ιB x) ≠ 0 := fun g h0 =>
    hX ((P.actQdR g).injective (h0.trans (map_zero _).symm))
  have hW : ∀ g : GQ l, P.actQdR g (P.ιB y * (P.ιB x)⁻¹ - U) = P.ιB y * (P.ιB x)⁻¹ - U := by
    intro g
    have h1 := congrArg P.ιB (hxy g)
    simp only [map_sub, map_mul, hcomm] at h1
    rw [map_sub, map_mul, map_inv₀, hU]
    have hx1 := mul_inv_cancel₀ hX
    have hx2 := mul_inv_cancel₀ (hgX g)
    linear_combination ((P.ιB x)⁻¹ * (P.actQdR g (P.ιB x))⁻¹) * h1
      - (P.actQdR g (P.ιB y) * (P.actQdR g (P.ιB x))⁻¹) * hx1 + (P.ιB y * (P.ιB x)⁻¹) * hx2
      + (P.ιB ((kummer P g : ℚ_[l]) • P.tB) * P.actQdR g (P.ιB x) * (P.actQdR g (P.ιB x))⁻¹) * hx1
      + P.ιB ((kummer P g : ℚ_[l]) • P.tB) * hx2
  obtain ⟨c, hc⟩ := (P.PD (botExt l)).invdR (P.ιB y * (P.ιB x)⁻¹ - U) fun g => by
    rw [P.PD_actdR]; exact hW g
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 c.2
  have hca : algebraMap ↥(botExt l).1 P.R.BdR c = algebraMap ℚ_[l] P.R.BdR a := by
    have e : c = algebraMap ℚ_[l] ↥(botExt l).1 a := Subtype.ext ha.symm
    rw [e, ← IsScalarTower.algebraMap_apply]
  rw [hca] at hc
  have hY : P.ιB (y - a • x) = P.ιB x * U := by
    rw [map_sub, map_smul, Algebra.smul_def]
    have hx1 := mul_inv_cancel₀ hX
    linear_combination (-P.ιB x) * hc - P.ιB y * hx1
  apply StLat.not_frac l Co ϖ hϖ u hu (T.eB x) (T.eB (y - a • x))
  · rw [← hC.ι]
    exact fun h0 => hX (T.eD.injective (h0.trans (map_zero _).symm))
  · rw [← hC.ι, ← hC.ι, hY, map_mul, hUdef, RingEquiv.apply_symm_apply]

theorem stRegular : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    IsDomain (Bst P) ∧
    (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 →
      (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') →
      ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) ∧
    (∀ (K : FinExt l) (b : Bst P), b ≠ 0 →
      (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) b = algebraMap ℚ_[l] (Bst P) x * b) → IsUnit b) := by
  intro l _ P AI ⟨T⟩
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hinj : Co.TensorInj := GlobalTheory.Published.FontaineBcris_holds.tensorInj Co
  have hreg : Co.Regular := GlobalTheory.Published.FontaineBcris_holds.regular Co
  refine ⟨inferInstance, fun K b b' hb h => ?_, fun K b hb h => ?_⟩
  · haveI : CharZero P.R.B := by
      have := (algebraMap ℚ_[l] P.R.B).injective
      exact charZero_of_injective_algebraMap this
    have hA : ∀ (g : GQ l) (p : Bst P), actSt P g p = (p.map ((P.actQ g).toRingEquiv : P.R.B →+* P.R.B)).comp (X + C ((kummer P g : ℚ_[l]) • P.tB)) :=
      fun g p => stHom_apply P (P.actQ g) _ p
    obtain ⟨d, d', hd, e, hf⟩ := GlobalTheory.T.twistedShift_fixed_ratio_const_domain (fun g : ↥(GK K) => (P.actQ (g : GQ l)).toRingEquiv)
      (fun g => (kummer P (g : GQ l) : ℚ_[l]) • P.tB)
      (fun d d' hd hh => StLat.kummer_not_frac l P AI T K d d' hd fun g hg => hh ⟨g, hg⟩) b' b hb (fun g => by
        rw [← hA, ← hA]; exact h g)
    obtain ⟨c, hc⟩ := GlobalTheory.RegularRing.fracInv hC hinj K d d' hd fun g => by
      rw [P.PD_actB, P.PD_actB]; exact hf g
    refine ⟨⟨c, c.2.2⟩, c.2.1, ?_⟩
    have hd' : (C d : Bst P) ≠ 0 := C_ne_zero.2 hd
    apply mul_left_cancel₀ hd'
    have hK0 : algebraMap ↥(K0 K) P.R.B c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, c.2.2⟩ := rfl
    rw [e, hc, Polynomial.algebraMap_apply, C_mul, hK0]
    ring
  · have hK : ∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB :=
      GlobalTheory.Pst.NoLog.kummer_not_coboundary l P AI T K
    exact GlobalTheory.T.isUnit_of_stable_line' l P K hK (GlobalTheory.RegularRing.lineUnit hC hreg K) b hb h

end GlobalTheory.Pst
