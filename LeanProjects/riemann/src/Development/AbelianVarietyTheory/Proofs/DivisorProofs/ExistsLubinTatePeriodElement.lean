import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusLiftLubinTateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfTiltCompatibleSequenceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCompatibleThetaZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatiblePowerSeriesValueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTorsionSequenceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EvaluationPowerSeriesShift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodThetaKernel

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK
open GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LTPeriodShape

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∃ (ω : AK K) (t u : BK K), thetaK K ω = 0 ∧ ω ∉ RingHom.ker (thetaK K) ^ 2 ∧
      t = toB K (ofA K ω) * (1 + toB K (ofA K ω) * u) ∧ ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  intro l _ K χ π z h
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
  have hq : resCard K = l ^ fK K := rfl
  have hsq : ω₀ ∉ RingHom.ker (thetaK K) ^ 2 :=
    GlobalTheory.LTPeriodKerSq.not_mem_sq hπ hne h0 (by rw [hq]; exact hω₀)
  obtain ⟨L', u₁, hL', hc, hu₁, ht⟩ := GlobalTheory.AcrisK.ev_shift l K _ (onDisc_log hπ hF) ω₀ h0 _ hev
  obtain ⟨L'', u, -, -, -, hu⟩ := GlobalTheory.AcrisK.ev_shift l K L' hL' ω₀ h0 u₁ hu₁
  refine ⟨ω₀, ltLog hπ hF ω₀ h0, u, h0, hsq, ?_, fun g => ?_⟩
  · rw [ht, hu, hc, PowerSeries.coeff_zero_eq_constantCoeff_apply, GlobalTheory.LTLog.constantCoeff_log _ hπ hF,
      GlobalTheory.LTLog.coeff_one_log _ hπ hF, map_zero, map_one, zero_add]
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

end GlobalTheory.LTPeriodShape

end
