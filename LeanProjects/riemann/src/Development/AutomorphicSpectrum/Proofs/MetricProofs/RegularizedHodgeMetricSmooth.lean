import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjSmoothAlong
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open MuRegSmooth TopNPoly in

theorem muReg_smooth_log : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ), S.IsTied → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg Hd S B t) ∧ (muReg Hd S B t).a = muTwDeg Hd B ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((muReg Hd S B t).h z) = Real.log (S.ref.h z) + S.regWeight t (M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B hS
  have hP : ProjSmoothAlong.Statement := ProjSmoothAlong.proof HoloInjDerivInj.proof GlobalTheory.T.local_orbit_chart_statement_holds
  have hVS : VertFactorSmooth.Statement := VertFactorSmooth.proof VertFactorPos.proof
  have hSB : ∀ p ∈ D.SB B, p ∈ D.S := fun p hp => (Finset.mem_filter.1 hp).1
  filter_upwards [regWeight_smooth S hS] with t ht
  have hPm : IsMultiHomogIdeal (mCoordIdeal D.y) := D.arith.2.1.2.1
  set F : ((Σ k, J k) → ℂ) → ℝ := fun z =>
    S.ref.h z * Real.exp (S.regWeight t (M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z with hFdef
  have hvpos : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ p ∈ D.SB B, 0 < D.vertFactor p z := fun z hz p hp =>
    VertFactorPos.proof II Ψ K J Ω W D p (hSB p hp) z hz
  have hpos : ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < F z := fun z hz =>
    mul_pos (mul_pos (S.ref.pos z hz.1) (Real.exp_pos _)) (Finset.prod_pos (hvpos z hz))
  have hhom : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ muTwDeg Hd B k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts (mCoordIdeal D.y) := mcPts_smul hPm c hc hz
    have hproj : M.proj (torusSmul c z) = M.proj z := ((M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ Hd.aMu k) * S.ref.h z := by
      rw [show torusSmul c z = fun p => c p.1 * z p from rfl, S.ref.smul c z hc, S.ref_deg]
      rfl
    have hvf : ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) =
        (∏ p ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p k) * ∏ p ∈ D.SB B, D.vertFactor p z := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p hp => (hVS II Ψ K J Ω W D p (hSB p hp)).1 z hz c hc
    simp only [hFdef]
    rw [href, hproj, hvf, muTwDeg, prod_norm_zpow_add_sum hc]
    ring
  have hsm : SmoothAlong (mcPts (mCoordIdeal D.y)) F :=
    smoothAlong_mul (smoothAlong_mul (smoothAlong_of_contDiffOn S.ref_smooth)
      (smoothAlong_exp (hP II Ψ K J Ω W D M _ ht)))
      (smoothAlong_prod _ fun p hp => (hVS II Ψ K J Ω W D p (hSB p hp)).2)
  obtain ⟨Z, hZa, hZs, hZh⟩ := HermExtend.proof K J (mCoordIdeal D.y) (muTwDeg Hd B) F hPm hpos hhom hsm
  have hagree : ∀ z ∈ mcPts (mCoordIdeal D.y), Z.h z =
      (hermOfFun J (muTwDeg Hd B) fun z => (S.regLine t).h z * ∏ p ∈ D.SB B, D.vertFactor p z).h z := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
    have hw0 := orbitRep_blocks hz.1
    have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
      have h := mcPts_smul hPm (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
      convert h using 1
      funext p
      have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
      rw [hp, ← _root_.mul_assoc, inv_mul_cancel₀ (hc _), _root_.one_mul]
    have hG0 : 0 < S.ref.h (orbitRep z) * Real.exp (S.regWeight t (M.proj (orbitRep z))) :=
      mul_pos (S.ref.pos _ hw0) (Real.exp_pos _)
    have hreg : (S.regLine t).h (orbitRep z) =
        S.ref.h (orbitRep z) * Real.exp (S.regWeight t (M.proj (orbitRep z))) :=
      hermOfFun_h_orbitRep hz.1 hG0
    have hFw : (S.regLine t).h (orbitRep z) * ∏ p ∈ D.SB B, D.vertFactor p (orbitRep z) = F (orbitRep z) := by
      rw [hreg]
    rw [hZh z hz, hermOfFun_h_smul hc hzc hz.1 (by rw [hFw]; exact hpos _ hwP), hFw]
    conv_lhs => rw [hzc]
    exact hhom _ hwP c hc
  refine ⟨?_, smoothRep_a _ _, fun z hz => ?_⟩
  · unfold muReg
    exact smoothRep_smooth_of (Z := Z) hZa hZs hagree
  · have hmu : (muReg Hd S B t).h z = F z := by
      unfold muReg
      rw [smoothRep_h _ hz, ← hagree z hz, hZh z hz]
    have h1 : S.ref.h z ≠ 0 := (S.ref.pos z hz.1).ne'
    have h2 : ∏ p ∈ D.SB B, D.vertFactor p z ≠ 0 := (Finset.prod_pos (hvpos z hz)).ne'
    rw [hmu]
    simp only [hFdef]
    rw [Real.log_mul (mul_ne_zero h1 (Real.exp_pos _).ne') h2, Real.log_mul h1 (Real.exp_pos _).ne',
      Real.log_exp, Real.log_prod fun p hp => (hvpos z hz p hp).ne']

end GlobalTheory.CompanionTheory.Ar.Cusp
