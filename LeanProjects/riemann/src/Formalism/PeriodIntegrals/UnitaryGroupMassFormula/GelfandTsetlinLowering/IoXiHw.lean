import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.IoPolDiagHw

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem io_fixed_up {n : ℕ} (lam : DomWeight (n + 1)) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hU : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) f = f)
    (a b : Fin n) (hab : a < b) : pol ℂ a.castSucc b.castSucc f = 0 := by
  have hne : a ≠ b := ne_of_lt hab
  have key : ∀ m : ℕ, (rowGen ℂ a.castSucc b.castSucc f - Polynomial.C f).eval (C (m : ℂ)) ∈
      (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) := by
    intro m
    rw [Submodule.mem_bot, Polynomial.eval_sub, Polynomial.eval_C, PI.WHw.eval_rowGen, sub_eq_zero]
    have hdet : (1 + Matrix.single a b (m : ℂ)).det ≠ 0 := by
      rw [det_one_add_single, if_neg hne]; exact one_ne_zero
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
    have hgv : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b (m : ℂ) := rfl
    have hup : ∀ i j, j < i → g i j = 0 := by
      intro i j hji
      have hij : i ≠ j := ne_of_gt hji
      show (1 + Matrix.single a b (m : ℂ)) i j = 0
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_neg hij, zero_add]
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact absurd (lt_trans hab hji) (lt_irrefl _)
    have hdiag : ∀ i, g i i = 1 := by
      intro i
      show (1 + Matrix.single a b (m : ℂ)) i i = 1
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_true]
      rw [if_neg]; · simp
      rintro ⟨rfl, h⟩; exact hne h.symm
    have h1 := hU g hup hdiag
    have hT := embGL_transvec g a b (m : ℂ) hgv
    have hdet1 : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl g) lam.detShift = 1 := by
      unfold detPow
      have hd : Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hT, det_one_add_single,
          if_neg (fun h => hne (Fin.castSucc_injective _ h).symm)]
        rfl)
      rw [hd, one_zpow, Units.val_one]
    unfold sqAct at h1
    rw [hdet1, one_smul, hT] at h1
    exact h1
  have := PI.WHw.coeff_mem_of_eval ⊥ _ key 1
  rw [Submodule.mem_bot, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by omega), sub_zero] at this
  rw [pol_eq_rowDiv]
  exact this

theorem io_torus_diag {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n)
    (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hT : ∀ t : Fin n → ℂˣ, sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl (diagGL ℂ n t)) f =
      ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) • f)
    (a : Fin n) (hd : lam.detShift ≤ sg.w a) :
    pol ℂ a.castSucc a.castSucc f = ((sg.w a - lam.detShift : ℤ) : ℂ) • f := by
  set d : ℕ := (sg.w a - lam.detShift).toNat with hd'
  have hdz : ((d : ℕ) : ℤ) = sg.w a - lam.detShift := Int.toNat_of_nonneg (by omega)
  have key : ∀ m : ℕ, (rowGen ℂ a.castSucc a.castSucc f - Polynomial.C f * (1 + Polynomial.X) ^ d).eval
      (C (m : ℂ)) ∈ (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) := by
    intro m
    have hm0 : (m : ℂ) + 1 ≠ 0 := by norm_cast
    let t : Fin n → ℂˣ := fun j => if j = a then Units.mk0 ((m : ℂ) + 1) hm0 else 1
    have h1 := hT t
    have hgv : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a a (m : ℂ) := by
      ext i j
      simp only [diagGL, Matrix.diagonal_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, t]
      by_cases hij : i = j <;> by_cases hia : i = a <;> simp_all [add_comm] <;> intro h <;> exact absurd h.symm hia
    have hTr := embGL_transvec (diagGL ℂ n t) a a (m : ℂ) hgv
    have hdet : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl (diagGL ℂ n t)) lam.detShift =
        ((m : ℂ) + 1) ^ lam.detShift := by
      unfold detPow
      rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hTr,
        det_one_add_single, if_pos rfl]
    have hprod : ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) = ((m : ℂ) + 1) ^ sg.w a := by
      rw [Finset.prod_eq_single a (fun j _ hj => by simp [t, hj]) (by simp), Units.val_zpow_eq_zpow_val]
      simp [t]
    unfold sqAct at h1
    rw [hdet, hTr, hprod] at h1
    have hz : ((m : ℂ) + 1) ^ sg.w a = ((m : ℂ) + 1) ^ lam.detShift * ((m : ℂ) + 1) ^ d := by
      rw [← zpow_natCast, hdz, ← zpow_add₀ hm0]
      congr 1
      ring
    rw [hz, ← smul_smul] at h1
    have h2 := smul_right_injective _ (zpow_ne_zero _ hm0) h1
    rw [Submodule.mem_bot, Polynomial.eval_sub, PI.WHw.eval_rowGen, sub_eq_zero, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
    rw [show (1 + C (m : ℂ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ^ d = C (((m : ℂ) + 1) ^ d) by
      rw [map_pow, map_add, map_one, add_comm (C (m : ℂ)) 1], mul_comm, ← smul_eq_C_mul]
    exact h2
  have := PI.WHw.coeff_mem_of_eval ⊥ _ key 1
  rw [Submodule.mem_bot, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
    Nat.choose_one_right, sub_eq_zero] at this
  rw [pol_eq_rowDiv]
  unfold rowDiv
  rw [this, ← hdz, Int.cast_natCast, smul_eq_C_mul, mul_comm, map_natCast]

theorem capXi (hx : XiFacts) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (hI : Interlace h lam sg) (u : ℂ) :
    Formalism.REAL.qdet (capE h lam) u (xi ℂ h lam sg) = capP sg u • xi ℂ h lam sg := by
  subst h
  obtain ⟨-, -, hU, hT, -, -⟩ := hx n (n + 1) rfl lam sg hI
  have hHW : Formalism.REAL.IsHW (capE rfl lam) (fun k => ((sg.w k : ℤ) : ℂ)) (xi ℂ rfl lam sg) := by
    refine ⟨fun a' => ?_, fun a' b' hab => ?_⟩
    · have hd : lam.detShift ≤ sg.w a' := by
        have ha := a'.isLt
        have h1 := (hI a').2
        have h2 : lam.w ⟨n, by omega⟩ ≤ lam.w ⟨a'.1 + 1, by omega⟩ := lam.anti (by
          rw [Fin.le_iff_val_le_val]
          show a'.1 + 1 ≤ n
          omega)
        have h3 : lam.detShift = lam.w ⟨n, by omega⟩ := by
          unfold DomWeight.detShift
          rw [dif_pos (by omega)] <;> congr 1
        linarith
      have e : pol ℂ (Fin.castLE (by omega : n ≤ n + 1) a') (Fin.castLE (by omega : n ≤ n + 1) a')
          (xi ℂ rfl lam sg) = ((sg.w a' - lam.detShift : ℤ) : ℂ) • xi ℂ rfl lam sg :=
        io_torus_diag lam sg (xi ℂ rfl lam sg) hT a' hd
      rw [capE_apply, if_pos rfl, e, ← add_smul]
      congr 1
      push_cast
      ring
    · have e : pol ℂ (Fin.castLE (by omega : n ≤ n + 1) a') (Fin.castLE (by omega : n ≤ n + 1) b')
          (xi ℂ rfl lam sg) = 0 :=
        io_fixed_up lam (xi ℂ rfl lam sg) hU a' b' hab
      rw [capE_apply, if_neg (ne_of_lt hab), e, add_zero]
  rw [Formalism.REAL.quantumDetHighestWeight_holds _ n (capE rfl lam) _ _ (capE_glRel rfl lam) hHW u]
  rfl

theorem capFacts_of (h3 : PI.HwIrred) (hx : XiFacts) : CapFacts := by
  intro n N h lam sg hI
  refine ⟨fun u => Formalism.REAL.qdet (capE h lam) u, ?_, ?_⟩
  · intro mu _ φ hφ s hs u
    exact capScalar h3 h lam mu φ hφ s hs u
  · intro u
    exact capXi hx h lam sg hI u

theorem ioExists_of' (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hx : XiFacts) : IoExists :=
  ioExists_of_cap h3 h4 hx (capFacts_of h3 hx)

end PI.WGL
