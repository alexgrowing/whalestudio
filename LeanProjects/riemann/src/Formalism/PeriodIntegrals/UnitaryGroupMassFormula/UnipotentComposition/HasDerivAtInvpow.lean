import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.StepOne

open Matrix MvPolynomial

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCompose

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_eval {σ : Type*} [Fintype σ] (v : ℝ → σ → ℂ) (v' : σ → ℂ)
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) 0) (q : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => eval (v t) q) (∑ i, eval (v 0) (pderiv i q) * v' i) 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simpa [pderiv_C] using hasDerivAt_const (0 : ℝ) a
  | add p q hp hq =>
    have hf : (fun t => eval (v t) (p + q)) = fun t => eval (v t) p + eval (v t) q := by
      funext t; simp
    rw [hf]
    refine (hp.add hq).congr_deriv ?_
    simp [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have hf : (fun t => eval (v t) (p * X i)) = fun t => eval (v t) p * v t i := by
      funext t; simp
    rw [hf]
    refine (hp.mul (hv i)).congr_deriv ?_
    symm
    · simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, eval_X, pderiv_X, add_mul,
        Finset.sum_add_distrib]
      rw [show ∀ a b c d : ℂ, b = c → a = d → a + b = c + d from
        fun a b c d h1 h2 => by rw [h1, h2, add_comm]]
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      · simp [Pi.single_apply, apply_ite (eval (v 0)), mul_ite, ite_mul, Finset.sum_ite_eq,
          Finset.sum_ite_eq']

theorem crv_var {k r : ℕ} (X g : Mat k r) (i : Vr (2 * r + k + 1)) :
    HasDerivAt (fun t => vars (crv (false, X) g t) i) (eval (vars g) (lin X i)) 0 := by
  have h := crv_hasDerivAt (false, X) g
  have hab : ∀ a b, HasDerivAt (fun t => crv (false, X) g t a b) ((g * X) a b) 0 := by
    intro a b
    have h1 := hasDerivAt_pi.1 h a
    have h2 := hasDerivAt_pi.1 h1 b
    simpa [dirv] using h2
  rcases i with ⟨a, b⟩ | ⟨a, b⟩
  · refine (hab a b).congr_deriv ?_
    simp only [lin, map_sum, map_mul, eval_C, eval_X, vars, Sum.elim_inl, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · refine (hab a b).star.congr_deriv ?_
    simp only [lin, map_sum, map_mul, eval_C, eval_X, vars, Sum.elim_inr, Matrix.mul_apply, star_sum, star_mul']
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem hasDerivAt_poly {k r : ℕ} (X g : Mat k r) (q : MvPolynomial (Vr (2 * r + k + 1)) ℂ) :
    HasDerivAt (fun t => eval (vars (crv (false, X) g t)) q) (eval (vars g) (dP X q)) 0 := by
  have h := hasDerivAt_eval (fun t => vars (crv (false, X) g t)) (fun i => eval (vars g) (lin X i))
    (fun i => crv_var X g i) q
  have h0 : crv (false, X) g 0 = g := by simp [crv]
  rw [h0] at h
  convert h using 1
  simp only [dP, map_sum, map_mul]

theorem eval_qD {k j ρ : ℕ} (g : Mat k (j + ρ)) : eval (vars g) (qD k j ρ) = DjU k j ρ g := by
  rw [qD, DjU, RingHom.map_det]
  congr 1
  ext a b
  simp [zP, Zh, vars]

theorem eval_qDb {k j ρ : ℕ} (g : Mat k (j + ρ)) : eval (vars g) (qDb k j ρ) = star (DjU k j ρ g) := by
  rw [qDb, DjU, RingHom.map_det, show star (Zh k j ρ g).det = (starRingEnd ℂ) (Zh k j ρ g).det from rfl,
    RingHom.map_det]
  congr 1
  ext a b
  simp [zPb, Zh, vars]

theorem hasDerivAt_invpow {c : ℝ → ℂ} {c' : ℂ} (hc : HasDerivAt c c' 0) (h0 : c 0 ≠ 0) (a : ℕ) :
    HasDerivAt (fun t => (c t)⁻¹ ^ a) (-(a : ℂ) * c' * (c 0)⁻¹ ^ (a + 1)) 0 := by
  have h2 := ((hasDerivAt_inv h0).pow a).comp (0 : ℝ) hc
  have hf : (fun t => (c t)⁻¹ ^ a) = ((fun y => y⁻¹) ^ a) ∘ c := by
    funext t; simp [Function.comp, Pi.pow_apply]
  rw [hf]
  refine h2.congr_deriv ?_
  rcases a with _ | a
  · simp
  · simp only [Nat.add_sub_cancel, inv_pow]
    field_simp
    ring

theorem hasDerivAt_sv {k j ρ : ℕ} (X g : Mat k (j + ρ)) (hg : DjU k j ρ g ≠ 0) (s : SC (2 * (j + ρ) + k + 1)) :
    HasDerivAt (fun t => sv k j ρ s (crv (false, X) g t))
      (sv k j ρ (dP X s.1, s.2.1, s.2.2) g
        + sv k j ρ (C (-(s.2.1 : ℂ)) * s.1 * dP X (qD k j ρ), s.2.1 + 1, s.2.2) g
        + sv k j ρ (C (-(s.2.2 : ℂ)) * s.1 * dP X (qDb k j ρ), s.2.1, s.2.2 + 1) g) 0 := by
  obtain ⟨q, a, b⟩ := s
  have hq := hasDerivAt_poly X g q
  have hD : HasDerivAt (fun t => DjU k j ρ (crv (false, X) g t))
      (eval (vars g) (dP X (qD k j ρ))) 0 := by
    simpa only [eval_qD] using hasDerivAt_poly X g (qD k j ρ)
  have hDb : HasDerivAt (fun t => star (DjU k j ρ (crv (false, X) g t)))
      (eval (vars g) (dP X (qDb k j ρ))) 0 := by
    simpa only [eval_qDb] using hasDerivAt_poly X g (qDb k j ρ)
  have h0 : crv (false, X) g 0 = g := by simp [crv]
  have hD0 : DjU k j ρ (crv (false, X) g 0) ≠ 0 := by rw [h0]; exact hg
  have hDb0 : star (DjU k j ρ (crv (false, X) g 0)) ≠ 0 := by rw [h0]; exact star_ne_zero.2 hg
  have h := (hq.mul (hasDerivAt_invpow hD hD0 a)).mul (hasDerivAt_invpow hDb hDb0 b)
  simp only [h0] at h
  refine h.congr_deriv ?_
  simp only [sv, map_mul, eval_C, Pi.mul_apply, h0]
  ring

end PI.UnitaryGroupMassFormula.UsCompose
