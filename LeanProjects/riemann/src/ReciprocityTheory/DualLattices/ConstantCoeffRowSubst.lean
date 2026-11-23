import ReciprocityTheory.DualLattices.FischerSmulRight

noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

theorem rowSubst_X (g : Matrix (Fin ν) (Fin ν) ℂ) (p : Fin ν × ι) :
    rowSubst g (X p) = ∑ l, C (g l p.1) * X (l, p.2) := by
  simp [rowSubst]

theorem rowSubst_C (g : Matrix (Fin ν) (Fin ν) ℂ) (c : ℂ) :
    rowSubst g (C c : MvPolynomial (Fin ν × ι) ℂ) = C c := by
  simp [rowSubst]

theorem constantCoeff_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    constantCoeff (rowSubst h Q) = constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [rowSubst_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp => simp [map_mul, hp, rowSubst_X]

theorem coeff_zero_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    coeff 0 (rowSubst h Q) = coeff 0 Q := by
  exact constantCoeff_rowSubst h Q

theorem pderiv_rowSubst_X (h : Matrix (Fin ν) (Fin ν) ℂ) (k : Fin ν) (a : ι) (s : Fin ν × ι) :
    pderiv (k, a) (rowSubst h (X s : MvPolynomial (Fin ν × ι) ℂ)) =
      if s.2 = a then C (h k s.1) else 0 := by
  rw [rowSubst_X, map_sum]
  by_cases hs : s.2 = a
  · simp [pderiv_C_mul, pderiv_X, Pi.single_apply, hs]
  · simp [pderiv_C_mul, pderiv_X, Pi.single_apply, hs]

theorem pderiv_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (k : Fin ν) (a : ι)
    (Q : MvPolynomial (Fin ν × ι) ℂ) :
    pderiv (k, a) (rowSubst h Q) = ∑ m, C (h k m) * rowSubst h (pderiv (m, a) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [rowSubst_C]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have e1 : ∀ m, rowSubst h (pderiv (m, a) (X n : MvPolynomial (Fin ν × ι) ℂ)) =
        if n = (m, a) then 1 else 0 := by
      intro m
      rw [pderiv_X, Pi.single_apply]
      split_ifs <;> simp
    have e2 : ∑ m, C (h k m) * (rowSubst h p * (if n = (m, a) then 1 else 0)) =
        rowSubst h p * (if n.2 = a then C (h k n.1) else 0) := by
      by_cases hn : n.2 = a
      · rw [if_pos hn, Finset.sum_eq_single n.1]
        · rw [if_pos (show n = (n.1, a) from Prod.ext rfl hn)]
          ring
        · intro m _ hm
          rw [if_neg (fun h' => hm (congrArg Prod.fst h').symm)]
          ring
        · intro h'
          exact absurd (Finset.mem_univ _) h'
      · rw [if_neg hn, mul_zero]
        refine Finset.sum_eq_zero (fun m _ => ?_)
        rw [if_neg (fun h' => hn (congrArg Prod.snd h'))]
        ring
    rw [map_mul, Derivation.leibniz, hp, pderiv_rowSubst_X, smul_eq_mul, smul_eq_mul, ← e2,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, e1]
    ring

theorem fischer_rowSubst (g : Matrix (Fin ν) (Fin ν) ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (rowSubst g P) Q = fischer P (rowSubst gᴴ Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    rw [rowSubst_C, fischer_C_left, fischer_C_left, coeff_zero_rowSubst]
  | add p q hp hq =>
    rw [map_add, fischer_add_left, fischer_add_left, hp, hq]
  | mul_X p n hp =>
    rcases n with ⟨k, a⟩
    rw [map_mul, rowSubst_X, Finset.mul_sum, fischer_sum_left, fischer_mul_X, pderiv_rowSubst,
      fischer_sum_right]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_left_comm, MvPolynomial.C_mul', fischer_smul_left, fischer_mul_X, hp, MvPolynomial.C_mul',
      fischer_smul_right]
    simp [Matrix.conjTranspose_apply]

end ReciprocityTheory.PGsh
