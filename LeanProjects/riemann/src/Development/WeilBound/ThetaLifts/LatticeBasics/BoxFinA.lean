import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.RealInv

noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped SchwartzMap
open GlobalTheory.ThK.Dbl.Dense Complex

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

structure Gau (f : 𝓢(V, ℂ)) (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) : Prop where
  ne : ∀ y, f y ≠ 0
  der : ∀ a y, fderiv ℝ f y a = m a y * f y
  symm : ∀ a y, m a y = m y a
  neg : ∀ a, a ≠ 0 → (m a a).re < 0

theorem gau_of {f : 𝓢(V, ℂ)} (hf : f ≠ 0) {m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ} (hm : ∀ a y, fderiv ℝ f y a = m a y * f y) : Gau f m := by
  obtain ⟨c, Q, Q', hc, pos, e⟩ := GlobalTheory.CompanionTheory.Twist.schwartz_logDeriv_linear_gaussian f hf m hm
  have ne : ∀ y, f y ≠ 0 := fun y => by rw [e]; exact mul_ne_zero hc (exp_ne_zero _)
  have key : ∀ a y, m a y = -((Q a y + Q y a : ℝ) : ℂ) - I * ((Q' a y + Q' y a : ℝ) : ℂ) := fun a y => by
    have l : HasDerivAt (fun t : ℝ => y + t • a) a 0 := by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add y
    have h1 : HasDerivAt (fun t : ℝ => f (y + t • a)) (fderiv ℝ f y a) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (f.differentiableAt (x := y)).hasFDerivAt l (by simp)
    have q : ∀ P : V →ₗ[ℝ] V →ₗ[ℝ] ℝ, HasDerivAt (fun t : ℝ => ((P (y + t • a) (y + t • a) : ℝ) : ℂ)) ((P a y + P y a : ℝ) : ℂ) 0 :=
      fun P => by
        have e1 : (fun t : ℝ => P (y + t • a) (y + t • a)) = fun t => P y y + t * (P a y + P y a) + t ^ 2 * P a a := by
          funext t; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]; ring
        have : HasDerivAt (fun t : ℝ => P (y + t • a) (y + t • a)) (P a y + P y a) 0 := by
          rw [e1]
          exact ((((hasDerivAt_id (0 : ℝ)).mul_const (P a y + P y a)).const_add (P y y)).fun_add
            ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (P a a))).congr_deriv (by simp)
        exact this.ofReal_comp
    have h2 := (((q Q).neg.sub ((q Q').const_mul I)).cexp).const_mul c
    have h3 : (fun t : ℝ => f (y + t • a)) = _ := funext fun t => e _
    rw [h3] at h1
    have h4 := h1.unique h2
    rw [hm] at h4
    refine mul_right_cancel₀ (ne y) (h4.trans ?_)
    rw [e]; simp; ring
  refine ⟨ne, hm, fun a y => by rw [key, key, add_comm (Q a y), add_comm (Q' a y)], fun a ha => ?_⟩
  have := pos a ha
  rw [key]; simp; linarith

theorem opp {f g : 𝓢(V, ℂ)} {m n : V →ₗ[ℝ] V →ₗ[ℝ] ℂ} (hf : Gau f m) (hg : Gau g n) {a b : V} {L L' : V →L[ℝ] ℝ}
    (h1 : dop b L' f = I • dop a L f) (h2 : dop (-b) (-L') g = I • dop a L g) : a = 0 ∧ L = 0 := by
  have e1 : ∀ y, m b y - 2 * Real.pi * I * L' y = I * (m a y - 2 * Real.pi * I * L y) := fun y => by
    have := congrArg (fun h : 𝓢(V, ℂ) => h y) h1
    simp only [SchwartzMap.smul_apply, dop_apply, hf.der, smul_eq_mul] at this
    exact mul_right_cancel₀ (hf.ne y) (by linear_combination this)
  have e2 : ∀ y, -n b y + 2 * Real.pi * I * L' y = I * (n a y - 2 * Real.pi * I * L y) := fun y => by
    have := congrArg (fun h : 𝓢(V, ℂ) => h y) h2
    simp only [SchwartzMap.smul_apply, dop_apply, hg.der, smul_eq_mul, map_neg, LinearMap.neg_apply,
      ContinuousLinearMap.neg_apply, ofReal_neg] at this
    exact mul_right_cancel₀ (hg.ne y) (by linear_combination this)
  have r1 := fun y => congrArg re (e1 y)
  have i1 := fun y => congrArg im (e1 y)
  have r2 := fun y => congrArg re (e2 y)
  have i2 := fun y => congrArg im (e2 y)
  simp at r1 i1 r2 i2
  have s1 := congrArg im (hf.symm a b)
  have s2 := congrArg im (hg.symm a b)
  have le : ∀ {h : 𝓢(V, ℂ)} {k} (_ : Gau h k) x, (k x x).re ≤ 0 := fun H x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (H.neg x hx).le
  have ha : a = 0 := by
    by_contra ha
    linarith [hf.neg a ha, hg.neg a ha, le hf b, le hg b, r1 b, r2 b, i1 a, i2 a]
  have hb : b = 0 := by
    by_contra hb
    linarith [hf.neg b hb, hg.neg b hb, le hf a, le hg a, r1 b, r2 b, i1 a, i2 a]
  refine ⟨ha, ContinuousLinearMap.ext fun y => ?_⟩
  have := r1 y
  simpa [ha, hb, Real.pi_ne_zero] using this

end GlobalTheory.ThK.Dbl.Box

end
