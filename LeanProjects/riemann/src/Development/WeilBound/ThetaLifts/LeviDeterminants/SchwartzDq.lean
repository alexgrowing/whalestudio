import Development.WeilBound.ThetaLifts.LeviDeterminants.DqStmt
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoundMulTranslate

open Complex GlobalTheory.CompanionTheory.OM.SchDiff
open scoped ContDiff

namespace PositivityTheory.ThKF0

theorem schwartzDq : SchwartzDq := by
  intro V _ _ _ a L f G hG T
  let ph : ℝ × V → ℝ := fun q => -(2 * Real.pi) * (q.1 * L q.2 + q.1 * q.1 * (L a / 2))
  let l : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight a
  have h1 := (ContinuousLinearMap.fst ℝ ℝ V).hasTemperateGrowth
  have h2 := (L ∘L ContinuousLinearMap.snd ℝ ℝ V).hasTemperateGrowth
  have hph : Function.HasTemperateGrowth ph :=
    (Function.HasTemperateGrowth.const _).fun_mul ((h1.fun_mul h2).fun_add
      ((h1.fun_mul h1).fun_mul (Function.HasTemperateGrowth.const _)))
  have hA := temperate_exp.comp hph
  let F : ℝ × V → ℂ := fun q => cexp (I * (ph q : ℝ)) * f (q.2 + l q.1)
  have hF : ContDiff ℝ ∞ F := hA.1.mul ((f.smooth ⊤).comp (contDiff_snd.add (l.contDiff.comp contDiff_fst)))
  have hR : ∀ t, ⇑(G t) = fun x => F (t, x) := fun t => by
    funext x
    rw [hG, Lib.hl]
    simp only [F, ph, l, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
    congr 2
    push_cast
    ring
  have hd : ∀ x, HasDerivAt (fun t => F (t, x)) (Lib.dop a L f x) 0 := fun x => by
    have e1 : HasDerivAt (fun t : ℝ => ph (t, x)) (-(2 * Real.pi) * L x) 0 := by
      have := ((((hasDerivAt_id (0 : ℝ)).mul_const (L x)).add
        (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (L a / 2))).const_mul (-(2 * Real.pi)))
      exact this.congr_deriv (by simp)
    have e2 := (e1.ofReal_comp.const_mul I).cexp
    have e3 : HasDerivAt (fun t : ℝ => f (x + l t)) (fderiv ℝ f x a) 0 := by
      have := (f.differentiable (x + l 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (l.hasDerivAt.const_add x)
      exact this.congr_deriv (by simp [l])
    refine (e2.mul e3).congr_deriv ?_
    rw [Lib.dop_apply]
    simp [ph, l]
    ring
  have hD : ∀ v : ℝ, ⇑((v : ℂ) • Lib.dop a L f) = fun x => fderiv ℝ F (0, x) (v, 0) := fun v => by
    funext x
    have e := (hF.differentiable (by simp) (0, x)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))
    have e' : fderiv ℝ F (0, x) (1, 0) = Lib.dop a L f x := e.unique (hd x)
    rw [show ((v, 0) : ℝ × V) = v • (1, 0) by simp, map_smul, e', SchwartzMap.smul_apply, smul_eq_mul, Complex.real_smul]
  have key := hasFDerivAt_family hF 0 (fun k n => bound_mul_translate hA f l 0 k n) G (fun v => (v : ℂ) • Lib.dop a L f) hR hD T
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (T (Lib.dop a L f))) fun v => by simp
  exact key.hasDerivAt.congr_deriv (by simp)

end PositivityTheory.ThKF0
