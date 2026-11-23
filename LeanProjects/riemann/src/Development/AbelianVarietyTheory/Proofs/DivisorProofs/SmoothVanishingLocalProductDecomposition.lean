import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DBaseApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothVanishingHyperplaneFactor
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge GlobalTheory.TorsionForm.Fibrewise
open scoped ContDiff

noncomputable section

namespace GlobalTheory.FibreHadamard

theorem fibre_hadamard : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g m : ℕ} (B : Set E) (r : Pt E g → Ext m), IsOpen B → ContDiffOn ℝ ∞ r (cov B g) → ∀ b ∈ B, (∀ z, r (b, z) = 0) → ∀ z : Fin g → ℂ, ∃ (N : ℕ) (ψ : Fin N → E → ℂ) (q : Fin N → Pt E g → Ext m), (∀ k, ContDiff ℝ ∞ (ψ k)) ∧ (∀ k, ψ k b = 0) ∧ (∀ k, ContDiff ℝ ∞ (q k)) ∧ r =ᶠ[𝓝 (b, z)] fun Q => ∑ k, ψ k Q.1 • q k Q := by
  intro E _ _ _ g m B r hB hr b hb h0 z
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 hB b hb
  let ρ : ContDiffBump b := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let rt : Pt E g → Ext m := fun Q => ρ Q.1 • r Q
  have hρsupp : tsupport (fun Q : Pt E g => ρ Q.1) ⊆ cov B g := by
    refine (tsupport_comp_subset_preimage (ρ : E → ℝ) continuous_fst).trans ?_
    intro Q hQ
    refine ⟨hεB ?_, mem_univ _⟩
    have hQ' : Q.1 ∈ tsupport (ρ : E → ℝ) := hQ
    rw [ρ.tsupport_eq] at hQ'
    exact Metric.closedBall_subset_ball (show ε / 2 < ε by linarith) hQ'
  have hrt_smooth : ContDiff ℝ ∞ rt := by
    rw [contDiff_iff_contDiffAt]
    intro Q
    by_cases hQ : Q ∈ cov B g
    · exact (ρ.contDiff.comp contDiff_fst).contDiffAt.smul
        (hr.contDiffAt ((hB.prod isOpen_univ).mem_nhds hQ))
    · have hQ' : Q ∉ tsupport (fun Q : Pt E g => ρ Q.1) := fun h => hQ (hρsupp h)
      have h1 : rt =ᶠ[𝓝 Q] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hQ'] with y hy
        have : ρ y.1 = 0 := image_eq_zero_of_notMem_tsupport (f := fun Q : Pt E g => ρ Q.1) hy
        simp [rt, this]
      exact contDiffAt_const.congr_of_eventuallyEq h1
  have hrt0 : ∀ w, rt (b, w) = 0 := fun w => by simp [rt, h0]
  have hd : ContDiff ℝ ∞ (fderiv ℝ rt) := hrt_smooth.fderiv_right (m := ∞) (by simp)
  have hdiff : Differentiable ℝ rt := hrt_smooth.differentiable (by simp)
  let e := Module.finBasis ℝ E
  let γ : Pt E g → ℝ → Pt E g := fun Q t => (b + t • (Q.1 - b), Q.2)
  have hcont : ∀ (Q : Pt E g) (v : Pt E g) (S : Finset (Fin m)),
      Continuous fun t => fderiv ℝ rt (γ Q t) v S := by
    intro Q v S
    have hγc : Continuous (γ Q) := by simp only [γ]; fun_prop
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset (Fin m) => ℂ) S).continuous.comp
      ((hd.continuous.comp hγc).clm_apply continuous_const)
  refine ⟨Module.finrank ℝ E, fun k b' => ((e.repr (b' - b) k : ℝ) : ℂ),
    fun k Q S => ∫ t in (0:ℝ)..1, fderiv ℝ rt (γ Q t) (e k, 0) S, ?_, ?_, ?_, ?_⟩
  · intro k
    have h1 : (fun b' : E => ((e.repr (b' - b) k : ℝ) : ℂ)) =
        fun b' => Complex.ofRealCLM (LinearMap.toContinuousLinearMap (e.coord k) (b' - b)) := by
      funext b'; simp
    change ContDiff ℝ ∞ (fun b' : E => ((e.repr (b' - b) k : ℝ) : ℂ))
    rw [h1]
    exact Complex.ofRealCLM.contDiff.comp
      ((LinearMap.toContinuousLinearMap (e.coord k)).contDiff.comp (contDiff_id.sub contDiff_const))
  · intro k; simp
  · intro k
    rw [contDiff_pi]
    intro S
    have hγ : ContDiff ℝ ∞ fun p : Pt E g × ℝ => γ p.1 p.2 := by
      simp only [γ]; fun_prop
    exact GlobalTheory.Chamber.contDiff_intervalIntegral_unit
      (Φ := fun p : Pt E g × ℝ => fderiv ℝ rt (γ p.1 p.2) (e k, 0) S)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset (Fin m) => ℂ) S).contDiff.comp
        ((hd.comp hγ).clm_apply contDiff_const))
  · have hnhds : {Q : Pt E g | Q.1 ∈ Metric.ball b (ε / 4)} ∈ 𝓝 (b, z) :=
      (Metric.isOpen_ball.preimage continuous_fst).mem_nhds (by simp; positivity)
    filter_upwards [hnhds] with Q hQ
    have hρ1 : ρ Q.1 = 1 := ρ.one_of_mem_closedBall (Metric.ball_subset_closedBall hQ)
    have hrQ : r Q = rt Q := by simp [rt, hρ1]
    rw [hrQ]
    funext S
    have hderiv : ∀ t, HasDerivAt (fun t => rt (γ Q t) S) (fderiv ℝ rt (γ Q t) (Q.1 - b, 0) S) t := by
      intro t
      have hγd : HasDerivAt (γ Q) (Q.1 - b, (0 : Fin g → ℂ)) t := by
        have h1 : HasDerivAt (fun t : ℝ => b + t • (Q.1 - b)) (Q.1 - b) t := by
          simpa using ((hasDerivAt_id t).smul_const (Q.1 - b)).const_add b
        exact h1.prodMk (hasDerivAt_const t Q.2)
      have h2 := (hdiff (γ Q t)).hasFDerivAt.comp_hasDerivAt t hγd
      exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset (Fin m) => ℂ) S).hasFDerivAt.comp_hasDerivAt t h2
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      ((hcont Q (Q.1 - b, 0) S).intervalIntegrable 0 1)
    have hγ1 : γ Q 1 = Q := by simp [γ]
    have hγ0 : γ Q 0 = (b, Q.2) := by simp [γ]
    simp only [hγ1, hγ0, hrt0, Pi.zero_apply, sub_zero] at hftc
    rw [← hftc]
    have hexp : ∀ t, fderiv ℝ rt (γ Q t) (Q.1 - b, 0) S =
        ∑ k, ((e.repr (Q.1 - b) k : ℝ) : ℂ) * fderiv ℝ rt (γ Q t) (e k, 0) S := by
      intro t
      have hv : ((Q.1 - b, (0 : Fin g → ℂ)) : Pt E g) =
          ∑ k, (e.repr (Q.1 - b) k) • ((e k, 0) : Pt E g) := by
        conv_lhs => rw [← e.sum_repr (Q.1 - b)]
        ext <;> simp [Prod.fst_sum, Prod.snd_sum]
      rw [hv, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Pi.smul_apply, Complex.real_smul]
    simp_rw [hexp]
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_const_mul, Pi.smul_apply, smul_eq_mul]
    · intro k _
      exact ((hcont Q (e k, 0) S).const_mul _).intervalIntegrable 0 1

end GlobalTheory.FibreHadamard
