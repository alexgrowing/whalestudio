import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.EopW
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementGelfandPolynomialFormula

noncomputable section

open NumberField Polynomial Finset Formalism.REAL

namespace PositivityTheory.RgBcC.Bridge

theorem epow_eq_pow {A : Type} [Ring A] {n : ℕ} (M : Fin n → Fin n → A) (k : ℕ) (i j : Fin n) :
    epow M k i j = ((Matrix.of M) ^ k) i j := by
  induction k generalizing i j with
  | zero => simp [epow, Matrix.one_apply]
  | succ k ih => simp only [epow, pow_succ, Matrix.mul_apply, ih, Matrix.of_apply]

theorem epow_succ' {A : Type} [Ring A] {n : ℕ} (M : Fin n → Fin n → A) (k : ℕ) (i j : Fin n) :
    epow M (k + 1) i j = ∑ c, M i c * epow M k c j := by
  rw [epow_eq_pow, pow_succ', Matrix.mul_apply]
  simp only [epow_eq_pow, Matrix.of_apply]

theorem defect_sub (t : ℕ → ℂ) (m N : ℕ) (P Q : ℂ[X]) (z : ℂ) :
    defect t m N (Q - C z * P) = defect t m N Q - C z * defect t m N P := by
  simp only [defect, sub_comp, mul_comp, C_comp]
  ring

theorem natDegree_le_of_coeff (p : ℂ[X]) (m : ℕ) (h1 : p.natDegree ≤ m + 1) (h2 : p.coeff (m + 1) = 0) :
    p.natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rcases Nat.lt_or_ge (m + 1) N with h | h
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h1 h)
  · have e : N = m + 1 := by omega
    subst e; exact h2

theorem defect_succ (t : ℕ → ℂ) (m N : ℕ) (D : ℂ[X]) :
    defect t m (N + 1) D = (X - C (m : ℂ)) * defect t m N D - C ((-1) ^ (N + 1) * t (N + 1)) * D := by
  simp only [defect]
  rw [sum_range_succ _ (N + 1)]
  have e : ∀ k ∈ range (N + 1), C ((-1) ^ k * t k) * (X - C (m : ℂ)) ^ (N + 1 - k) =
      (X - C (m : ℂ)) * (C ((-1) ^ k * t k) * (X - C (m : ℂ)) ^ (N - k)) := by
    intro k hk
    have : N + 1 - k = (N - k) + 1 := by have := mem_range.mp hk; omega
    rw [this, pow_succ]; ring
  rw [sum_congr rfl e, ← mul_sum, Nat.sub_self, pow_zero]
  ring

theorem natDegree_comp_sub_le (P : ℂ[X]) (d : ℕ) (hd : P.natDegree = d + 1) :
    (P.comp (X + 1) - P).natDegree ≤ d := by
  have hP : P ≠ 0 := by intro h; rw [h] at hd; simp at hd
  have hqd : (X + 1 : ℂ[X]).natDegree = 1 := by simpa using natDegree_X_add_C (1 : ℂ)
  have hql : (X + 1 : ℂ[X]).leadingCoeff = 1 := by simpa using leadingCoeff_X_add_C (1 : ℂ)
  have h2 : (P.comp (X + 1)).natDegree = d + 1 := by rw [natDegree_comp, hqd, hd, mul_one]
  have hl : (P.comp (X + 1)).leadingCoeff = P.leadingCoeff := by
    rw [leadingCoeff_comp (by rw [hqd]; norm_num), hql, one_pow, mul_one]
  have h1 : P.comp (X + 1) ≠ 0 := by intro h; rw [h] at h2; simp at h2
  by_cases h0 : P.comp (X + 1) - P = 0
  · rw [h0]; simp
  have hlt := degree_sub_lt_left (by rw [degree_eq_natDegree h1, degree_eq_natDegree hP, h2, hd]) h1 hl
  rw [degree_eq_natDegree h1, h2, degree_eq_natDegree h0] at hlt
  exact Nat.lt_succ_iff.mp (by exact_mod_cast hlt)

theorem coeff_comp_sub (P : ℂ[X]) (d : ℕ) (hd : P.natDegree = d + 1) :
    (P.comp (X + 1) - P).coeff d = ((d : ℂ) + 1) * P.leadingCoeff := by
  have e1 : P.comp (X + 1) = taylor 1 P := by rw [taylor_apply, map_one]
  rw [coeff_sub, e1, taylor_coeff]
  have hdeg : (hasseDeriv d P).natDegree < 2 := by
    rw [natDegree_hasseDeriv, hd]; omega
  rw [eval_eq_sum_range' hdeg, sum_range_succ, sum_range_one, hasseDeriv_coeff, hasseDeriv_coeff]
  simp only [zero_add, Nat.choose_self, Nat.cast_one, one_mul, pow_zero, mul_one, one_pow]
  rw [leadingCoeff, hd, add_comm 1 d, Nat.choose_succ_self_right]
  push_cast
  ring

theorem monic_capQ (m : ℕ) (χ : Fin (m + 1) → ℂ) : (∏ s, (X + C (χ s - (m : ℂ) / 2))).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem natDegree_capQ (m : ℕ) (χ : Fin (m + 1) → ℂ) : (∏ s, (X + C (χ s - (m : ℂ) / 2))).natDegree = m + 1 := by
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem coeff_defect_gelf (m : ℕ) (χ : Fin (m + 1) → ℂ) (N : ℕ) :
    (defect (GlobalTheory.Dec.gelfVal χ) m N (∏ s, (X + C (χ s - (m : ℂ) / 2)))).coeff (m + 1) = 0 := by
  set P : ℂ[X] := ∏ s, (X + C (χ s - (m : ℂ) / 2)) with hP
  have hG := GlobalTheory.T.trace_element_gelfand_polynomial_formula m χ N
  rw [← hP] at hG
  set G : ℂ[X] := (X - C (m : ℂ)) ^ (N + 1) * (P.comp (X + 1) - P) -
    P * ∑ k ∈ range N, C ((-1) ^ k * GlobalTheory.Dec.gelfVal χ k) * (X - C (m : ℂ)) ^ (N - k) with hGd
  have hdef : defect (GlobalTheory.Dec.gelfVal χ) m N P = G - P * C ((-1) ^ N * GlobalTheory.Dec.gelfVal χ N) := by
    simp only [defect, hGd, sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    ring
  have hneg : ((-1 : ℂ[X]) ^ N) = C ((-1 : ℂ) ^ N) := by simp
  rw [hneg, coeff_C_mul] at hG
  have hPc : P.coeff (m + 1) = 1 := by
    have := (monic_capQ m χ).coeff_natDegree
    rwa [natDegree_capQ] at this
  have hsq : ((-1 : ℂ) ^ N) * ((-1 : ℂ) ^ N) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  rw [hdef, coeff_sub, coeff_mul_C, hPc, one_mul]
  linear_combination ((-1 : ℂ) ^ N) * hG - (G.coeff (m + 1)) * hsq

theorem natDegree_defect_gelf (m : ℕ) (χ : Fin (m + 1) → ℂ) (N : ℕ) :
    (defect (GlobalTheory.Dec.gelfVal χ) m N (∏ s, (X + C (χ s - (m : ℂ) / 2)))).natDegree ≤ m := by
  set P : ℂ[X] := ∏ s, (X + C (χ s - (m : ℂ) / 2)) with hP
  have hPd : P.natDegree = m + 1 := natDegree_capQ m χ
  have hXm : (X - C (m : ℂ)).natDegree = 1 := natDegree_X_sub_C _
  induction N with
  | zero =>
    refine natDegree_le_of_coeff _ _ ?_ (coeff_defect_gelf m χ 0)
    simp only [defect, zero_add, pow_one, sum_range_one, Nat.sub_self, pow_zero, mul_one]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_mul_le).trans ?_
      rw [hXm]; have := natDegree_comp_sub_le P m hPd; omega
    · refine (natDegree_mul_le).trans ?_
      rw [hPd, natDegree_C]
  | succ N ih =>
    refine natDegree_le_of_coeff _ _ ?_ (coeff_defect_gelf m χ (N + 1))
    rw [defect_succ]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_mul_le).trans ?_
      rw [hXm]; omega
    · exact (natDegree_C_mul_le _ _).trans hPd.le

theorem natDegree_defect_op (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (M : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V) (hM : GlRel M) (v : V) (t : ℕ → ℂ)
    (ht : ∀ k, etr M k v = t k • v) (f : Module.Dual ℂ V) (Q : ℂ[X])
    (hQ : ∀ u : ℂ, Q.eval u = f (qdet M u v)) (N : ℕ) :
    (defect t m N Q).natDegree ≤ m := by
  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → Module.End ℂ V, ∀ w : ℂ,
      qminor M (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap (Module.End ℂ V) (m + 1) m M (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let Rc : ℕ → Module.End ℂ V := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * cm i j d * epow M (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
      (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * qminor M (Fin.succAbove j) (Fin.succAbove i) w
        * epow M (N + 1) j i = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  set Rp := GlobalTheory.CapelliNewton.polyOf m Rc f v with hRp
  have key : defect t m N Q = -(C ((-1 : ℂ) ^ N) * Rp) := by
    refine Polynomial.funext fun w => ?_
    have h1 := congrArg (fun T : Module.End ℂ V => f (T v)) (GlobalTheory.T.traced_qminor_comatrix_truncated_inverse (Module.End ℂ V) m M hM w N)
    rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', hR] at h1
    have h2 : (qdet M w * ∑ k ∈ range (N + 1), algebraMap ℂ (Module.End ℂ V) ((-1) ^ k * (w - m) ^ (N - k)) * etr M k) v
        = (∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * t k) • qdet M w v := by
      rw [Module.End.mul_apply, LinearMap.sum_apply, map_sum, sum_smul]
      refine sum_congr rfl fun k _ => ?_
      rw [Module.End.mul_apply, ht k, Module.algebraMap_end_apply, smul_smul, map_smul]
    rw [h2] at h1
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_add, map_smul,
      LinearMap.sub_apply, map_sub, smul_eq_mul] at h1
    rw [← GlobalTheory.CapelliNewton.polyOf_eval, ← hRp] at h1
    simp only [defect, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_comp, eval_add, eval_one, eval_finsetSum,
      eval_neg, hQ]
    have h3 : ∑ k ∈ range (N + 1), (-1) ^ k * t k * (w - m) ^ (N - k)
        = ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * t k :=
      sum_congr rfl fun k _ => by ring
    rw [h3]
    linear_combination h1
  rw [key, natDegree_neg]
  exact (natDegree_C_mul_le _ _).trans (GlobalTheory.CapelliNewton.polyOf_natDegree _ _ _ _)

theorem eq_zero_of_defect (m : ℕ) (t : ℕ → ℂ) (ht : t 0 = (m : ℂ) + 1) (D : ℂ[X]) (hD : D.natDegree ≤ m)
    (h : (defect t m (m + 1) D).natDegree ≤ m) : D = 0 := by
  by_contra hD0
  set N := m + 1 with hN
  set S : ℂ[X] := ∑ k ∈ range (N + 1), C ((-1) ^ k * t k) * (X - C (m : ℂ)) ^ (N - k) with hS
  have hXp : ∀ j : ℕ, ((X - C (m : ℂ)) ^ j).natDegree = j := fun j => by
    rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
  have hXc : ∀ j : ℕ, ((X - C (m : ℂ)) ^ j).coeff j = 1 := fun j => by
    have := ((monic_X_sub_C (m : ℂ)).pow j).coeff_natDegree
    rwa [hXp] at this
  have hSd : S.natDegree ≤ N := by
    refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [hXp]; omega
  have hSc : S.coeff N = (m : ℂ) + 1 := by
    rw [hS, sum_range_succ', coeff_add, finsetSum_coeff, sum_eq_zero]
    · rw [zero_add, coeff_C_mul, Nat.sub_zero, hXc, pow_zero, one_mul, mul_one, ht]
    · intro k _
      apply coeff_eq_zero_of_natDegree_lt
      refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
      rw [hXp]; omega
  set d := D.natDegree with hd
  have ha : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hD0
  have hzero : (defect t m N D).coeff (N + d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hDS : (D * S).coeff (d + N) = D.leadingCoeff * ((m : ℂ) + 1) := by
    rw [coeff_mul_add_eq_of_natDegree_le le_rfl hSd, hSc]; rfl
  rcases Nat.eq_zero_or_eq_succ_pred d with h0 | h0
  ·
    have hc : D = C (D.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    have hΔ : D.comp (X + 1) - D = 0 := by rw [hc, C_comp, sub_self]
    simp only [defect, hΔ, mul_zero, zero_sub, coeff_neg] at hzero
    rw [← hS, add_comm, hDS] at hzero
    apply ha
    have h1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have := neg_eq_zero.mp hzero
    exact (mul_eq_zero.mp this).resolve_right h1
  · set d' := d.pred with hd'
    have hdd : D.natDegree = d' + 1 := by omega
    have hΔd := natDegree_comp_sub_le D d' hdd
    have hΔc := coeff_comp_sub D d' hdd
    have hP1 : ((X - C (m : ℂ)) ^ (N + 1) * (D.comp (X + 1) - D)).coeff (N + 1 + d') = ((d' : ℂ) + 1) * D.leadingCoeff := by
      rw [coeff_mul_add_eq_of_natDegree_le (hXp _).le hΔd, hXc, one_mul, hΔc]
    have e : N + d = N + 1 + d' := by omega
    have e2 : N + d = d + N := by omega
    simp only [defect] at hzero
    rw [coeff_sub, ← hS] at hzero
    rw [e] at hzero
    rw [hP1, ← e, e2, hDS] at hzero
    have hne : ((d' : ℂ) + 1) - ((m : ℂ) + 1) ≠ 0 := by
      rw [sub_ne_zero]; intro h'
      have : (d' + 1 : ℕ) = m + 1 := by exact_mod_cast h'
      omega
    apply ha
    have : (((d' : ℂ) + 1) - ((m : ℂ) + 1)) * D.leadingCoeff = 0 := by linear_combination hzero
    exact (mul_eq_zero.mp this).resolve_left hne

theorem gelfVal_zero' {n : ℕ} (χ : Fin n → ℂ) : GlobalTheory.Dec.gelfVal χ 0 = n := by
  simp [GlobalTheory.Dec.gelfVal, Matrix.one_apply]

theorem gelfToCap (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (M : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V) (χ : Fin (m + 1) → ℂ) (v : V) (hM : GlRel M)
    (hv : ∀ k, etr M k v = GlobalTheory.Dec.gelfVal χ k • v) (Y : ℂ) :
    qdet M (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP χ Y • v := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun f => ?_
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) M
  set Q := GlobalTheory.CapelliNewton.polyOf (m + 1) c f v with hQd
  have hQ : ∀ u : ℂ, Q.eval u = f (qdet M u v) := fun u => by rw [hQd, GlobalTheory.CapelliNewton.polyOf_eval, hc]
  set P : ℂ[X] := ∏ s, (X + C (χ s - (m : ℂ) / 2)) with hP
  set D := Q - C (f v) * P with hDd
  have hQc : Q.coeff (m + 1) = f v := by rw [hQd, GlobalTheory.CapelliNewton.polyOf_coeff, hc1]; rfl
  have hPc : P.coeff (m + 1) = 1 := by
    have := (monic_capQ m χ).coeff_natDegree
    rwa [natDegree_capQ] at this
  have hDdeg : D.natDegree ≤ m := by
    refine natDegree_le_of_coeff _ _ ?_ ?_
    · refine (natDegree_sub_le _ _).trans (max_le (GlobalTheory.CapelliNewton.polyOf_natDegree _ _ _ _) ?_)
      exact (natDegree_C_mul_le _ _).trans (natDegree_capQ m χ).le
    · rw [hDd, coeff_sub, coeff_C_mul, hQc, hPc, mul_one, sub_self]
  have hdef : (defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) D).natDegree ≤ m := by
    rw [hDd, defect_sub]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_defect_op V m M hM v _ hv f Q hQ (m + 1)
    · exact (natDegree_C_mul_le _ _).trans (natDegree_defect_gelf m χ (m + 1))
  have h0 := eq_zero_of_defect m (GlobalTheory.Dec.gelfVal χ) (by rw [gelfVal_zero']; push_cast; ring) D hDdeg hdef
  have hev := congrArg (fun p : ℂ[X] => p.eval (Y + (m : ℂ) / 2)) h0
  simp only [hDd, eval_sub, eval_mul, eval_C, eval_zero, hQ, hP, eval_prod, eval_add, eval_X] at hev
  have e1 : (((m + 1 : ℕ) : ℂ) - 1) / 2 = (m : ℂ) / 2 := by push_cast; ring
  rw [e1, map_sub, map_smul, smul_eq_mul, Formalism.QuantumDeterminants.capP]
  have e2 : ∏ s, (Y + (m : ℂ) / 2 + (χ s - (m : ℂ) / 2)) = ∏ s, (Y + χ s) :=
    prod_congr rfl fun s _ => by ring
  rw [e2] at hev
  linear_combination hev

end PositivityTheory.RgBcC.Bridge
