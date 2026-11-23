import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

private theorem hermOfFun_h_eq_of_homogeneous_of_pos {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hF : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    (hpos : 0 < F z) : (hermOfFun ι a F).h z = F z := by
  have h0 : (torusSetoid (ι := ι)).r (orbitRep z) z := Quotient.mk_out (s := torusSetoid) z
  obtain ⟨c, hc, hcz⟩ := h0
  have ho : orbitRep z = torusSmul (fun k => (c k)⁻¹) z := by
    funext p
    conv_rhs => rw [hcz]
    simp only [torusSmul]
    rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]
  have hc' : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have hpc : 0 < ∏ k, ‖(c k)⁻¹‖ ^ a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc' k)) _
  have hr := refNorm_pos a hz
  show refNorm a z * Real.exp (Real.log (F (orbitRep z) / refNorm a (orbitRep z))) = F z
  rw [ho, hF _ hc', refNorm_smul, mul_div_mul_left _ _ hpc.ne', Real.exp_log (div_pos hpos hr)]
  field_simp

private theorem smoothRep_h_eq_of_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (A : HermLine ι) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) :
    (smoothRep P A).h z = A.h z := by
  unfold smoothRep
  split_ifs with h
  · exact h.choose_spec.2.2 z hz
  · rfl

private theorem eval_torusSmul_map_eq_eval_mConeMap {K : Type} {ι : K → Type} (c : K → ℂ) (z : (Σ k, ι k) → ℂ)
    (f : MRing ι) :
    eval (torusSmul c z) (map (Int.castRingHom ℂ) f) = MvPolynomial.eval c (mConeMap z f) := by
  have h : (eval (torusSmul c z)).comp (map (Int.castRingHom ℂ)) =
      (MvPolynomial.eval c).comp (mConeMap z).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · intro q
      simp [mConeMap, torusSmul, mul_comm]
  exact RingHom.congr_fun h f

private theorem torusSmul_mem_mcPts_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    torusSmul c z ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hf' : f ∈ mCoordIdeal z := VertFactorPos.mCoordIdeal_le hz hf
    rw [eval_torusSmul_map_eq_eval_mConeMap, RingHom.mem_ker.1 hf', map_zero]

theorem muReg_h_eq_of_mem_mcPts : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ), ∀ z ∈ mcPts (mCoordIdeal D.y), (muReg X.H X.S B t).h z = X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B t z hz
  have hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz.1
  have hpos := VertFactorPos.proof II Ψ K ι Ω E D
  have hsm := VertFactorSmooth.proof VertFactorPos.proof II Ψ K ι Ω E D
  have hproj : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → X.M.proj (torusSmul c z) = X.M.proj z := fun c hc =>
    ((X.M.fibre z hz (torusSmul c z) (torusSmul_mem_mcPts_mCoordIdeal D.y hz hc)).2 ⟨c, hc, rfl⟩).symm
  have hreg : (X.S.regLine t).h z = X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) := by
    refine hermOfFun_h_eq_of_homogeneous_of_pos (muLine X.H).a
      (fun w => X.S.ref.h w * Real.exp (X.S.regWeight t (X.M.proj w))) z hz' ?_
      (mul_pos (X.S.ref.pos z hz') (Real.exp_pos _))
    intro c hc
    show X.S.ref.h (torusSmul c z) * Real.exp (X.S.regWeight t (X.M.proj (torusSmul c z))) =
      (∏ k, ‖c k‖ ^ (muLine X.H).a k) * (X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)))
    have hs : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ (muLine X.H).a k) * X.S.ref.h z := by
      rw [← X.S.ref_deg]
      exact X.S.ref.smul c z hc
    rw [hproj c hc, hs, mul_assoc]
  rw [muReg, smoothRep_h_eq_of_mem_mcPts _ _ z hz]
  refine (hermOfFun_h_eq_of_homogeneous_of_pos (muTwDeg X.H B)
    (fun w => (X.S.regLine t).h w * ∏ p ∈ D.SB B, D.vertFactor p w) z hz' ?_ ?_).trans ?_
  · intro c hc
    show (X.S.regLine t).h (torusSmul c z) * ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) =
      (∏ k, ‖c k‖ ^ muTwDeg X.H B k) * ((X.S.regLine t).h z * ∏ p ∈ D.SB B, D.vertFactor p z)
    have h1 : (X.S.regLine t).h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * (X.S.regLine t).h z :=
      (X.S.regLine t).smul c z hc
    have h2 : ∀ p ∈ D.SB B,
        D.vertFactor p (torusSmul c z) = (∏ k, ‖c k‖ ^ D.vdeg p k) * D.vertFactor p z :=
      fun p hp => (hsm p (Finset.mem_filter.1 hp).1).1 z hz c hc
    rw [h1, Finset.prod_congr rfl h2, Finset.prod_mul_distrib, muTwDeg,
      MuRegSmooth.prod_norm_zpow_add_sum hc]
    ring
  · exact mul_pos ((X.S.regLine t).pos z hz')
      (Finset.prod_pos fun p hp => hpos p (Finset.mem_filter.1 hp).1 z hz)
  · show (X.S.regLine t).h z * ∏ p ∈ D.SB B, D.vertFactor p z = _
    rw [hreg]

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
