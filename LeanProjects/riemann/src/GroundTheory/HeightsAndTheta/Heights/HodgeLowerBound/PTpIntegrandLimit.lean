import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTpIntegrandLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBoundaryPtsNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RegWeightLimits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Set

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem log_metric_factor {x v a s : ℝ} (hx : 0 < x) (hv : 0 < v) (ha : 0 < a) (q p : ℕ) :
    Real.log ((x * Real.exp s) ^ q * v ^ q * a ^ p) =
      q * (Real.log x + s) + q * Real.log v + p * Real.log a := by
  have hxe : 0 < x * Real.exp s := mul_pos hx (Real.exp_pos s)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_mul hx.ne' (Real.exp_pos s).ne', Real.log_exp]

theorem log_hermOfFun_h (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hw : ∀ k, ∃ i, orbitRep z ⟨k, i⟩ ≠ 0) (hF : F (orbitRep z) ≠ 0) :
    Real.log ((hermOfFun ι a F).h z) =
      Real.log (refNorm a z) + Real.log (F (orbitRep z)) - Real.log (refNorm a (orbitRep z)) := by
  show Real.log (refNorm a z * Real.exp (Real.log (F (orbitRep z) / refNorm a (orbitRep z)))) = _
  rw [Real.log_mul (refNorm_pos a hz).ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_div hF (refNorm_pos a hw).ne']
  ring

omit [DecidableEq Ψ] in

theorem ComponentSetting.wSt_eq (X : ComponentSetting D O Lt) (B p q : ℕ) (hq : 1 ≤ q)
    (t t' : ℝ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    X.wSt B p q t t' z = (Real.log (X.S'.ref.h z) - Real.log (X.S.ref.h z)) +
      X.S'.bregWeight t' (X.M.proj z) - X.S.regWeight t (X.M.proj z) := by
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  have hJ : IsMultiHomogIdeal (mCoordIdeal D.y) := D.arith.2.1.2.1
  have hweq : (fun p : Σ k, ι k => (c p.1)⁻¹ * z p) = orbitRep z := by
    funext p'
    have e : z p' = c p'.1 * orbitRep z p' := congrFun hzc p'
    rw [e, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have hw : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
    rw [← hweq]
    exact mcPts_smul hJ (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
  have hproj : X.M.proj (orbitRep z) = X.M.proj z := (X.M.fibre _ hw z hz).2 ⟨c, hc, hzc⟩
  have hVpos : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z) :=
    Finset.prod_pos fun p' hp' => VertFactorPos.proof _ _ _ _ _ _ D p' (Finset.mem_filter.1 hp').1 _ hw
  have hA : 0 < D.A'.h (orbitRep z) := D.A'.pos _ hw.1
  have h0' : 0 < X.S'.ref.h (orbitRep z) := X.S'.ref.pos _ hw.1
  have h0 : 0 < X.S.ref.h (orbitRep z) := X.S.ref.pos _ hw.1
  have hdeg : X.S'.ref.a = X.S.ref.a := by rw [X.S'.ref_deg, X.S.ref_deg]; rfl
  have hratio := log_ratio_torusSmul X.S'.ref X.S.ref hdeg c hc hw.1
  rw [← hzc] at hratio
  have hMU : (X.MUq B p q t').h z = (hermOfFun ι ((q : ℤ) • muTwDeg X.H B + (p : ℤ) • D.a') fun z =>
      (X.S'.ref.h z * Real.exp (X.S'.bregWeight t' (X.M.proj z))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p).h z := smoothRepConj_h _ hz
  have hN : (X.NbarQ B p q t).h z = (hermOfFun ι ((q : ℤ) • muTwDeg X.H B + (p : ℤ) • D.a') fun z =>
      (X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p).h z := smoothRep_h _ hz
  have hF₁ := log_metric_factor h0' hVpos hA q p (s := X.S'.bregWeight t' (X.M.proj (orbitRep z)))
  have hF₂ := log_metric_factor h0 hVpos hA q p (s := X.S.regWeight t (X.M.proj (orbitRep z)))
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold ComponentSetting.wSt
  rw [hMU, hN, log_hermOfFun_h _ _ hz.1 hw.1 (by positivity), log_hermOfFun_h _ _ hz.1 hw.1 (by positivity),
    hF₁, hF₂, hproj, hratio]
  field_simp
  ring

theorem TpIntegrandLimit.proof (hBd : BoundaryPtsNull.Statement) :
    TpIntegrandLimit.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hq
  have hdeg : X.S'.ref.a = X.S.ref.a := by rw [X.S'.ref_deg, X.S.ref_deg]; rfl
  obtain ⟨CL, hCL⟩ := X.M.exists_bound_log_ratio X.S'.ref X.S.ref hdeg X.S'.ref_smooth X.S.ref_smooth
  have hLc : ContinuousOn (fun z => Real.log (X.S'.ref.h z) - Real.log (X.S.ref.h z))
      (mcPts (mCoordIdeal D.y)) :=
    (continuousOn_log_ratio X.S'.ref X.S.ref X.S'.ref_smooth X.S.ref_smooth).mono fun z hz => hz.1
  obtain ⟨Cb, hBev⟩ := X.S'.bregWeight_bounds X.S'_tied
  obtain ⟨t₁, ht₁, hreg⟩ := exists_Ioo_of_eventually_nhdsGT (X.S.continuous_regWeight X.S_tied)
  obtain ⟨s₀, hs₀, hbreg⟩ := exists_Ioo_of_eventually_nhdsGT hBev
  refine ⟨t₁ / 2, by linarith, fun t ht0 ht => ?_⟩
  have hrc : Continuous (X.S.regWeight t) := hreg t ht0 (by linarith)
  obtain ⟨Cr, hCr⟩ := (isCompact_univ : IsCompact (univ : Set X.M.Xc)).exists_bound_of_continuousOn
    hrc.continuousOn
  refine ⟨D.Bd, CL + Cb + Cr, s₀, hs₀, hBd II Ψ K ι Ω E D, fun t' ht' ht's => ⟨fun z hz => ?_, ?_⟩,
    fun z hz hzN => ?_⟩
  · rw [X.wSt_eq B p q hq t t' hz]
    have e1 := abs_le.1 (hCL z hz)
    have e2 := abs_le.1 ((hbreg t' ht' ht's).1 (X.M.proj z))
    have e3 := abs_le.1 (by simpa [Real.norm_eq_abs] using hCr (X.M.proj z) (mem_univ _))
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]
  · have hcont : ContinuousOn (fun z => (Real.log (X.S'.ref.h z) - Real.log (X.S.ref.h z)) +
        X.S'.bregWeight t' (X.M.proj z) - X.S.regWeight t (X.M.proj z)) (mcPts (mCoordIdeal D.y)) :=
      (hLc.add ((hbreg t' ht' ht's).2.comp_continuousOn X.M.cont)).sub (hrc.comp_continuousOn X.M.cont)
    exact (hcont.mono sdiff_subset).congr fun z hz => X.wSt_eq B p q hq t t' hz.1
  · have heq : (fun t' => X.wSt B p q t t' z) = fun t' =>
        (Real.log (X.S'.ref.h z) - Real.log (X.S.ref.h z)) + X.S'.bregWeight t' (X.M.proj z) -
          X.S.regWeight t (X.M.proj z) :=
      funext fun t' => X.wSt_eq B p q hq t t' hz
    rw [heq]
    have hXo : z ∈ D.Xo ∩ mcPts (mCoordIdeal D.y) := ⟨⟨hz, hzN⟩, hz⟩
    have hlim := X.S'.tendsto_bregWeight X.S'_tied (X.M.proj z)
    rw [X.S'.ph_eq z hXo] at hlim
    have := (hlim.const_add (Real.log (X.S'.ref.h z) - Real.log (X.S.ref.h z))).sub_const
      (X.S.regWeight t (X.M.proj z))
    convert this using 2
    ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
