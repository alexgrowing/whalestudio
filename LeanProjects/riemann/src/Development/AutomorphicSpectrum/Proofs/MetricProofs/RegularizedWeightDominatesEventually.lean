import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcSmooth
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.BRegWeightLevi
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RegWeightLimits
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjSmoothAlong
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section Metric

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W} {w : ((Σ k, J k) → ℂ) → ℝ}

theorem MUc_h_of_mem (Hd : HodgeData D) {M : XModel D} (S : BoundedRegularisationSetting M D.Xo Hd.aMu w) (B p q : ℕ) (t : ℝ)
    {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    (MUc Hd S B p q t).h z = (S.ref.h z * Real.exp (S.bregWeight t (M.proj z))) ^ q *
      (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p := by
  set P := mCoordIdeal D.y with hPdef
  set a : K → ℤ := (q : ℤ) • muTwDeg Hd B + (p : ℤ) • D.a' with ha
  set F : ((Σ k, J k) → ℂ) → ℝ := fun z => (S.ref.h z * Real.exp (S.bregWeight t (M.proj z))) ^ q *
    (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p with hFdef
  have hVS : VertFactorSmooth.Statement := VertFactorSmooth.proof VertFactorPos.proof
  have hSB : ∀ p' ∈ D.SB B, p' ∈ D.S := fun p' hp' => (Finset.mem_filter.1 hp').1
  have hMH : IsMultiHomogIdeal P := D.arith.2.1.2.1
  have hpos : ∀ z ∈ mcPts P, 0 < F z := by
    intro z hz
    have h2 : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' z := Finset.prod_pos fun p' hp' =>
      VertFactorPos.proof II Ψ K J Ω W D p' (hSB p' hp') z hz
    exact mul_pos (mul_pos (pow_pos (mul_pos (S.ref.pos z hz.1) (Real.exp_pos _)) q) (pow_pos h2 q))
      (pow_pos (D.A'.pos z hz.1) p)
  have hhom : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts P := mcPts_smul hMH c hc hz
    have hproj : M.proj (torusSmul c z) = M.proj z := ((M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ Hd.aMu k) * S.ref.h z := by
      have := S.ref.smul c z hc
      rw [S.ref_deg] at this
      exact this
    have hA : D.A'.h (torusSmul c z) = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h z := by
      have := D.A'.smul c z hc
      rw [D.A'_deg] at this
      exact this
    have hV : ∀ p' ∈ D.SB B, D.vertFactor p' (torusSmul c z) =
        (∏ k, ‖c k‖ ^ D.vdeg p' k) * D.vertFactor p' z :=
      fun p' hp' => (hVS II Ψ K J Ω W D p' (hSB p' hp')).1 z hz c hc
    have hk : ∀ k, ‖c k‖ ^ a k = (‖c k‖ ^ (muTwDeg Hd B) k) ^ q * (‖c k‖ ^ D.a' k) ^ p := by
      intro k
      have hx : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      have hak : a k = (q : ℤ) * (muTwDeg Hd B) k + (p : ℤ) * D.a' k := by
        simp only [ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hak, zpow_add₀ hx, _root_.zpow_mul', zpow_natCast, _root_.zpow_mul', zpow_natCast]
    have hprod : (∏ k, ‖c k‖ ^ a k) = ((∏ k, ‖c k‖ ^ Hd.aMu k) *
        ∏ p' ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p' k) ^ q * (∏ k, ‖c k‖ ^ D.a' k) ^ p := by
      rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
        muTwDeg, MuRegSmooth.prod_norm_zpow_add_sum hc]
    simp only [hFdef]
    rw [hproj, href, hA, Finset.prod_congr rfl hV, Finset.prod_mul_distrib, hprod]
    ring
  show (smoothRepConj P (hermOfFun J a F)).h z = F z
  rw [smoothRepConj_h _ hz]
  exact NbarSmooth.hermOfFun_h_of_mem hMH hhom hz (hpos z hz)

theorem log_MUc_h_of_mem (Hd : HodgeData D) {M : XModel D} (S : BoundedRegularisationSetting M D.Xo Hd.aMu w) (B p q : ℕ) (t : ℝ)
    {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    Real.log ((MUc Hd S B p q t).h z) = q * (Real.log (S.ref.h z) + S.bregWeight t (M.proj z) +
      ∑ r ∈ D.SB B, Real.log (D.vertFactor r z)) + p * Real.log (D.A'.h z) := by
  have hSB : ∀ p' ∈ D.SB B, 0 < D.vertFactor p' z := fun p' hp' =>
    VertFactorPos.proof II Ψ K J Ω W D p' (Finset.mem_filter.1 hp').1 z hz
  have h1 : S.ref.h z ≠ 0 := (S.ref.pos z hz.1).ne'
  have h2 : D.A'.h z ≠ 0 := (D.A'.pos z hz.1).ne'
  have h3 : ∏ p' ∈ D.SB B, D.vertFactor p' z ≠ 0 := (Finset.prod_pos hSB).ne'
  have h4 : S.ref.h z * Real.exp (S.bregWeight t (M.proj z)) ≠ 0 := mul_ne_zero h1 (Real.exp_pos _).ne'
  rw [MUc_h_of_mem Hd S B p q t hz, Real.log_mul (mul_ne_zero (pow_ne_zero _ h4) (pow_ne_zero _ h3)) (pow_ne_zero _ h2),
    Real.log_mul (pow_ne_zero _ h4) (pow_ne_zero _ h3), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul h1 (Real.exp_pos _).ne', Real.log_exp, Real.log_prod fun r hr => (hSB r hr).ne']
  ring

end Metric

theorem bregWeight_ge_and_MUc_smooth : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), S'.IsTied → ∀ᶠ t' in 𝓝[>] (0 : ℝ), (∀ x, S'.B.ph x ≤ S'.bregWeight t' x) ∧ M.atlas.Smooth (S'.bregWeight t') ∧ ∀ B p q : ℕ, IsSmoothHerm (MUc Hd S' B p q t') ∧ (MUc Hd S' B p q t').a = (q : ℤ) • muTwDeg Hd B + (p : ℤ) • D.a' ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((MUc Hd S' B p q t').h z) = q * (Real.log (S'.ref.h z) + S'.bregWeight t' (M.proj z) + ∑ r ∈ D.SB B, Real.log (D.vertFactor r z)) + p * Real.log (D.A'.h z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M w S' hS
  obtain ⟨δ, hδ, hmarg⟩ := S'.B.toPotentialCharts.exists_margin
  have hδ' : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < δ :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun t ht => ht.2
  have hMU := GroundTheory.Heights₂.Heights.NineStatements.MUcSmooth.proof HermExtend.proof
    (ProjSmoothAlong.proof HoloInjDerivInj.proof GlobalTheory.T.local_orbit_chart_statement_holds)
  filter_upwards [self_mem_nhdsWithin, hδ', S'.eventually_chartLevi hS] with t ht htδ hlev
  have ht' : 0 < t := ht
  have hε : 0 < S'.e1 t := lt_of_lt_of_le ht' (S'.e1_ge t ht')
  refine ⟨fun x => boundedPsh_le_regularised S'.B S'.ρ S'.cutoff hmarg ht' htδ.le hε x, hlev.1,
    fun B p q => ⟨hMU II Ψ K J Ω W D Hd M w S' B p q t hlev.1, smoothRepConj_a _ _,
      fun z hz => log_MUc_h_of_mem Hd S' B p q t hz⟩⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
