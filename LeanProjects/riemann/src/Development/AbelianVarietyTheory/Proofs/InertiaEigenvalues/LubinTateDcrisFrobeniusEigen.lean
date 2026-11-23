import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusLiftLubinTateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfTiltCompatibleSequenceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCompatibleThetaZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatiblePowerSeriesValueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTorsionSequenceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorInjectiveUnitRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusOrderOnMaxUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EvaluationPowerSeriesShiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingNoZeroDivisorsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaExtensionToCompleteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedWittElementEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodTensorMapInjective
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PZ.ColmezVec

theorem ev_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (L : PowerSeries ↥K.1), OnDisc l (oK K) L →
    PowerSeries.constantCoeff L = 0 → PowerSeries.coeff 1 L = 1 → ∀ (x : AK K), thetaK K x = 0 → x ≠ 0 →
    ∀ y : GlobalTheory.AcrisK.BK K, Ev L x y → y ≠ 0 := by
  intro l _ K L hL h0 h1 x hx hx0 y hy e
  obtain ⟨L', u, hL', hc, hu, hyu⟩ := GlobalTheory.T.evaluation_power_series_shift l K L hL x hx y hy
  obtain ⟨L'', u', -, -, -, hu'⟩ := GlobalTheory.T.evaluation_power_series_shift l K L' hL' x hx u hu
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.theta_extension_to_complete l K
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero, zero_add, e] at hyu
  have h2 := congrArg ψ hu'
  rw [GlobalTheory.T.period_ring_no_zero_divisors l K x hx0 u hyu.symm, hc, zero_add, h1, map_zero, map_one, map_add, map_one, map_mul, hψ, hx] at h2
  simp at h2

theorem exists_period (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l)
    (h : LTData K χ π z) : ∃ t : GlobalTheory.AcrisK.BK K, t ≠ 0 ∧ frobB K t = inK K (π : ↥K.1) * t ∧
      ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  obtain ⟨hπ, hF, v, hv0, hv1, hv, hg⟩ := GlobalTheory.T.lubin_tate_torsion_sequence l K χ π z h
  have hπu := GlobalTheory.LTTilt.not_isUnit_intToOC K hπ
  have hcomp : ∀ n, v (n + 1) ^ (l ^ fK K) - v n ∈ Ideal.span {intToOC K π} := fun n =>
    Ideal.mem_span_singleton.2 ⟨-v (n + 1), by rw [← hv n]; ring⟩
  obtain ⟨x, hx, -⟩ := GlobalTheory.LTTilt.existsUnique_isTiltOf (fK K) (NeZero.pos _) (intToOC K π) hπu
    (GlobalTheory.LTTilt.natCast_mem_span_intToOC K hπ) v hcomp
  obtain ⟨ω₀, hred, hω₀⟩ := GlobalTheory.T.exists_frobenius_lift_lubin_tate l K π hπ x
  choose r hr using (frobq_bijective K).2
  let ω : ℕ → AK K := fun n => r^[n] ω₀
  have hch : ∀ n, frobq K (ω (n + 1)) = ω n := fun n => by
    simp only [ω, Function.iterate_succ_apply', hr]
  have hθ : ∀ n, thetaK K (ω n) = v n := GlobalTheory.T.theta_of_tilt_compatible_sequence l K π hπ v ω hv (hred ▸ hx) hch hω₀
  have h0 : thetaK K ω₀ = 0 := (hθ 0).trans hv0
  have hne : ω₀ ≠ 0 := fun e => hv1 (by
    have : ω 1 = 0 := (frobq_bijective K).1 (by rw [hch, map_zero]; exact e)
    rw [← hθ, this, map_zero])
  have hker : ∀ (M : ℕ) (y : AK K), ω₀ ^ M ∣ y → y ∈ RingHom.ker (thetaK K) ^ M := fun M y ⟨c, hc⟩ =>
    hc ▸ Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (show ω₀ ∈ RingHom.ker (thetaK K) from h0) M)
  have hev := ev_ltLog hπ hF ω₀ h0
  refine ⟨ltLog hπ hF ω₀ h0, ev_ne_zero l K _ (onDisc_log hπ hF) (GlobalTheory.LTLog.constantCoeff_log _ hπ hF)
    (GlobalTheory.LTLog.coeff_one_log _ hπ hF) ω₀ h0 hne _ hev, ?_, fun g => ?_⟩
  · refine ev_log_self hπ hF h0 (fun n => hker n _ ?_) hev.frob
    have hq : resCard K = l ^ fK K := rfl
    have e : ∀ j, inO K (PowerSeries.coeff j (ltSeries K π)) * ω₀ ^ j =
        (if j = 1 then inO K π * ω₀ ^ j else 0) + if j = l ^ fK K then ω₀ ^ j else 0 := fun j => by
      rw [ltSeries, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, hq]
      split_ifs <;> simp [add_mul]
    simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, hω₀]
    rw [add_sub_add_comm]
    refine dvd_add ?_ ?_
    · split_ifs with h1
      · simp
      · rw [sub_zero]
        exact Dvd.dvd.mul_left (by simpa using pow_dvd_pow ω₀ (not_lt.1 h1)) _
    · split_ifs with h1
      · simp
      · rw [sub_zero]
        exact pow_dvd_pow ω₀ (not_lt.1 h1)
  · obtain ⟨a, ha, hs⟩ := hg g
    obtain ⟨y, hy1, hy2, hy3⟩ := GlobalTheory.T.exists_compatible_power_series_value l K ω (lubinTateHom hπ hF hF a).toPowerSeries
      (fun n => Per.σO (g : GQ l) (v n)) hch
      (fun n => by rw [hθ]; exact GlobalTheory.LTTilt.norm_lt_one_of_compat K hπ hcomp hv0 n)
      (fun n => by rw [hθ]; exact hs n)
    have hy : gal K g ω₀ = y 0 := sub_eq_zero.1 (GlobalTheory.T.frobenius_compatible_theta_zero l K (fun n => gal K g (ω n) - y n)
      (fun n => by rw [map_sub, hy1, ← gal_frobq, hch])
      (fun n => by rw [map_sub, hy2, thetaK_gal, hθ, sub_self]))
    rw [← ha]
    exact ev_log_hom hπ hF a h0 (fun n => hker n _ (hy ▸ hy3 n)) (hev.gal g)

section Abstract

variable {G : Type} [Group G] {Q K₀ K : Type} [Field Q] [Field K₀] [Field K]
    [Algebra Q K₀] [Algebra Q K] [Algebra K₀ K] [IsScalarTower Q K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Q B] [Algebra K₀ B] [IsScalarTower Q K₀ B]
    [Algebra Q BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Q K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Q K₀ BdR]
    (PD : PeriodData G Q K₀ K B BdR)

theorem pow_phi_algebraMap (k : ℕ) (c : K₀) : (PD.φ ^ k) (algebraMap _ B c) = algebraMap _ B ((⇑PD.σ)^[k] c) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, ih, PD.φ_K₀, Function.iterate_succ_apply']

def phiPow (f : ℕ) (hσ : ∀ c, (⇑PD.σ)^[f] c = c) : B →ₐ[K₀] B where
  toRingHom := (PD.φ ^ f).toRingHom
  commutes' := fun c => (pow_phi_algebraMap PD _ c).trans (congrArg _ (hσ c))

end Abstract

theorem ext_BK {l : ℕ} [Fact l.Prime] {K : FinExt l} {S : Type} [CommRing S] (u v : GlobalTheory.AcrisK.BK K →+* S)
    (hK : ∀ c, u (inK K c) = v (inK K c)) (hA : ∀ a, u (toB K (inC K a)) = v (toB K (inC K a))) : u = v := by
  refine ringHom_extB fun c => ?_
  refine RingHom.congr_fun (GlobalTheory.AcrisK.ringHom_ext (u := u.comp (toB K)) (v := v.comp (toB K)) hA fun c => ?_) c
  simp only [RingHom.comp_apply, ← inK_oK, hK]

section Tied

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (K : FinExt l)

theorem pow_phi_acris (k : ℕ) (a : Per.Acris l) :
    ((P.PD K).φ ^ k) (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) a)) =
      T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) ((⇑(phiA l))^[k] a)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, Function.iterate_succ_apply', P.PD_φ]
    apply T.eB.injective
    rw [T.frob, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, ← plusToB_alg, ← plusToB_alg,
      ← plusToB_phi, phiP_alg]

theorem act_acris (g : ↥(GK K)) (a : Per.Acris l) :
    (P.PD K).actB g (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) a)) =
      T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) (sigA (g : GQ l) a)) := by
  apply T.eB.injective
  rw [P.PD_actB, T.actB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, ← plusToB_alg, ← plusToB_alg,
    ← plusToB_sig, sigP_alg]

end Tied

end GlobalTheory.PZ.ColmezVec

end
