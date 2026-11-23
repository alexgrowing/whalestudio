import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelTupleSumEqRational
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorsLattice

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

namespace GlobalTheory.ThetaSumLevi

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y Topology Filter

theorem levi_lower {n : ℕ} {ι : Type} (s : Finset ι) {g : ι → V n → ℂ} {D : V n → ℂ}
    {φ : V n → ℝ} {z : V n} (c d : ℝ) (hg : ∀ t, ContDiffAt ℂ 2 (g t) z) (hD : ContDiffAt ℂ 2 D z)
    (hD0 : D z ≠ 0) (hφ : ContDiffAt ℝ 2 φ z) (hpos : 0 < ∑ t ∈ s, Complex.normSq (g t z))
    (ξ : Fin n → ℂ) :
    -(c * (leviV n (fun w => ((φ w : ℝ) : ℂ)) z ξ).re) ≤
      (leviV n (fun w => ((Real.log (∑ t ∈ s, Complex.normSq (g t w)) +
        ((c * Real.log (Complex.normSq (D w)) + d) + (-c) * φ w) : ℝ) : ℂ)) z ξ).re := by
  have hS : ContDiffAt ℝ 2 (fun w => Real.log (∑ t ∈ s, Complex.normSq (g t w))) z :=
    (ContDiffAt.sum fun t _ => contDiffAt_normSq_comp (hg t)).log hpos.ne'
  have hL : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (D w))) z :=
    (contDiffAt_normSq_comp hD).log (Complex.normSq_pos.2 hD0).ne'
  have hL' : ContDiffAt ℝ 2 (fun w => c * Real.log (Complex.normSq (D w)) + d) z :=
    (contDiffAt_const.mul hL).add contDiffAt_const
  have hφ' : ContDiffAt ℝ 2 (fun w => (-c) * φ w) z := contDiffAt_const.mul hφ
  have e : ∀ w, ∑ t ∈ s, Complex.normSq (g t w) =
      ∑ i : Fin s.card, Complex.normSq (g (s.equivFin.symm i) w) := fun w => by
    rw [← Finset.sum_coe_sort s]
    exact (s.equivFin.symm.sum_comp fun t => Complex.normSq (g t w)).symm
  have h0 := leviV_log_sum_nonneg (u := fun (i : Fin s.card) w => Complex.normSq (g (s.equivFin.symm i) w))
    (x := z) (fun i => contDiffAt_normSq_comp (hg _)) (fun i => logPshAt_normSq (hg _))
    (by rw [← e]; exact hpos) ξ
  simp only [← e] at h0
  rw [LocalMaximumSecondDerivative.leviV_ofReal_add hS (hL'.add hφ'), LocalMaximumSecondDerivative.leviV_ofReal_add hL' hφ',
    leviV_const_mul hL, leviV_log_normSq hD hD0, LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ hφ]
  simp only [mul_zero, zero_add, Complex.add_re, Complex.re_ofReal_mul]
  linarith

theorem levi_log_theta_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ ps : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)) → ∀ x0 ∈ X.dom, ∀ z, cpt X.toData x0 z ∈ X.dom → ∀ ξ : Fin (nd X.toData) → ℂ, -((r : ℝ) / 2 * leviM X.toData (phla X.toData (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1)) x0 z ξ) ≤ leviM X.toData ps x0 z ξ := by
  intro E _ _ _ r X _ hw ps hps x0 _ z hz ξ
  obtain ⟨Θ, D, κ, hκ, hΘ, hD, hD0, hval⟩ := GlobalTheory.ThetaHol.normalised_theta_norm_holomorphic E r X hw
  obtain ⟨𝒯, h1, h2⟩ := GlobalTheory.LevelTupleSum.exists_reps X.Λ X.Λ_fg
  set la : Wt X.Ψ r := fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1 with hla
  have hO := ExF.isOpen_OmF X.toData x0
  have hz' : z ∈ OmF X.toData x0 := hz
  have hc : Differentiable ℂ (cpt X.toData x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
      (IW.cpt_entry_cd X.toData x0 τ a b).differentiable (by simp)
  have hhol : ∀ {P : Frame X.Ψ r → ℂ}, DifferentiableOn ℂ P X.dom →
      ContDiffAt ℂ 2 (fun w => P (cpt X.toData x0 w)) z := fun hP =>
    contDiffAt_two_of_holo hO (hP.comp hc.differentiableOn fun _ hw => hw) hz'
  have key : ∀ w ∈ OmF X.toData x0,
      0 < ∑ t ∈ 𝒯, Complex.normSq (∏ b, Θ (t b) (cpt X.toData x0 w)) ∧
      ps (cpt X.toData x0 w) = Real.log (∑ t ∈ 𝒯, Complex.normSq (∏ b, Θ (t b) (cpt X.toData x0 w))) +
        (((r : ℝ) / 2 * Real.log (Complex.normSq (D (cpt X.toData x0 w))) + r * Real.log κ) +
          (-((r : ℝ) / 2)) * phla X.toData la (cpt X.toData x0 w)) := by
    intro w hw
    have hN : 0 < X.nfac la (cpt X.toData x0 w) := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_pos X.toData x0 hw
    have hx : cpt X.toData x0 w ∈ X.dom := hw
    generalize cpt X.toData x0 w = x at hN hx
    obtain ⟨A, hA⟩ := hps x hx
    have hp := GlobalTheory.TupleSumPos.tuple_sum_pos E r X x A
    have hs := GlobalTheory.LevelTupleSum.sum_eq hx A 𝒯 h1 h2 _ (GlobalTheory.LevelTupleSum.torus_r A)
    rw [hs] at hA hp
    have hDp : 0 < ‖D x‖ := norm_pos_iff.2 (hD0 x hx)
    have hK : 0 < (κ * ‖D x‖ * X.nfac la x) ^ r := by positivity
    have e : ∑ t ∈ 𝒯, ∏ b, A.T.ptN2 1 A.s (fun _ => A.φ (t b)) / A.T.l2 1 A.s =
        (κ * ‖D x‖ * X.nfac la x) ^ r * ∑ t ∈ 𝒯, Complex.normSq (∏ b, Θ (t b) x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_prod, ← Fin.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hval x hx A, Complex.normSq_eq_norm_sq]
      ring
    rw [e] at hA hp
    have hS := (mul_pos_iff_of_pos_left hK).1 hp
    refine ⟨hS, ?_⟩
    rw [hA, Real.log_mul hK.ne' hS.ne', Real.log_pow, Real.log_mul (by positivity) hN.ne',
      Real.log_mul hκ.ne' hDp.ne', IW.log_norm_eq, phla]
    ring
  have hev : (fun w => ((ps (cpt X.toData x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z] fun w =>
      ((Real.log (∑ t ∈ 𝒯, Complex.normSq (∏ b, Θ (t b) (cpt X.toData x0 w))) +
        (((r : ℝ) / 2 * Real.log (Complex.normSq (D (cpt X.toData x0 w))) + r * Real.log κ) +
          (-((r : ℝ) / 2)) * phla X.toData la (cpt X.toData x0 w)) : ℝ) : ℂ) := by
    filter_upwards [hO.mem_nhds hz'] with w hw
    rw [(key w hw).2]
  unfold leviM
  rw [leviV_congr hev]
  exact levi_lower 𝒯 (g := fun t w => ∏ b, Θ (t b) (cpt X.toData x0 w)) _ _
    (fun t => contDiffAt_prod fun b _ => hhol (hΘ _)) (hhol hD) (hD0 _ hz)
    ((IW.phla_cpt_cdAt X.toData x0 hz' la).of_le (by norm_cast)) (key z hz').1 ξ

end GlobalTheory.ThetaSumLevi
