import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TopOddNeEnd

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem symVar_inj (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    Function.Injective (symVar C0 CE1 CE2 X j) := by
  rintro (⟨a, c⟩ | ⟨l, b⟩) (⟨a', c'⟩ | ⟨l', b'⟩) h
  · simp only [symVar] at h
    have ha2 := a.2
    have ha2' := a'.2
    split_ifs at h with h1 h2 h2
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨e1, e2⟩, e3⟩ := h
      have e1' : (a : ℕ) / 2 = (a' : ℕ) / 2 := congrArg Fin.val (topOdd_inj X j e1)
      have e2' := decide_eq_decide.1 e2
      have hc : c = c' := Fin.succ_injective _ e3
      have ha : a = a' := Fin.ext (by omega)
      rw [ha, hc]
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1 (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1.symm (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨-, e2⟩, e3⟩ := h
      have e2' := decide_eq_decide.1 e2
      have hc : c = c' := Fin.succ_injective _ e3
      have ha : a = a' := Fin.ext (by omega)
      rw [ha, hc]
  · exfalso
    simp only [symVar] at h
    split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> exact Fin.succ_ne_zero _ h.2
  · exfalso
    simp only [symVar] at h
    split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> exact Fin.succ_ne_zero _ h.2.symm
  · simp only [symVar] at h
    have hl2 := l.2
    have hl2' := l'.2
    split_ifs at h with h1 h2 h2
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨e1, e2⟩, -⟩ := h
      have e1' : (X.seg C0 CE1 CE2 j).sigma + (l : ℕ) = (X.seg C0 CE1 CE2 j).sigma + (l' : ℕ) :=
        congrArg Fin.val (topOdd_inj X j e1)
      have hl : l = l' := Fin.ext (by omega)
      have hb : b = b' := by simpa using e2
      rw [hl, hb]
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1 (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1.symm (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨-, e2⟩, -⟩ := h
      have hl : l = l' := Fin.ext (by omega)
      have hb : b = b' := by simpa using e2
      rw [hl, hb]

theorem symLev_pos (C0 CE1 CE2 : ℝ) (X : Loc) (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (v : BV C0 CE1 CE2 X j) :
    0 < symLev X.p C0 CE1 CE2 X j v := by
  rcases v with ⟨a, c⟩ | ⟨l, b⟩
  · simp only [symLev]
    split_ifs
    · exact pow_pos hp _
    · exact one_pos
  · simp only [symLev]
    split_ifs
    · exact pow_pos hp _
    · exact one_pos

theorem coarse_eval (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (μ : BV C0 CE1 CE2 X j →₀ ℕ)
    (v0 : BV C0 CE1 CE2 X j) :
    (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n))
      (symVar C0 CE1 CE2 X j v0) = symLev X.p C0 CE1 CE2 X j v0 * μ v0 := by
  classical
  rw [Finsupp.sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finsupp.sum, Finset.sum_eq_single v0]
  · simp
  · intro v _ hv
    rw [if_neg fun e => hv (symVar_inj C0 CE1 CE2 X j e)]
  · intro hv
    simp [Finsupp.notMem_support_iff.1 hv]

theorem ioExp_inj (C0 CE1 CE2 : ℝ) (X : Loc) (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) :
    Function.Injective (ioExp C0 CE1 CE2 X j b) := by
  intro μ μ' h
  unfold ioExp at h
  have h' := add_left_cancel h
  ext v0
  have := DFunLike.congr_fun h' (symVar C0 CE1 CE2 X j v0)
  rw [coarse_eval, coarse_eval] at this
  exact Nat.eq_of_mul_eq_mul_left (symLev_pos C0 CE1 CE2 X hp j v0) this

theorem ioBlock_monomial (C0 CE1 CE2 : ℝ) (X : Loc) (K : Type) [Field K] (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (μ : BV C0 CE1 CE2 X j →₀ ℕ) (c : K) :
    ioBlock K X.p C0 CE1 CE2 X j b (monomial μ c) = monomial (ioExp C0 CE1 CE2 X j b μ) c := by
  classical
  have hd : digitMon K C0 CE1 CE2 X j b = monomial (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
      (Finsupp.single ((topOdd X j i, true), c) (b.rz i c) + Finsupp.single ((topOdd X j i, false), c) (b.ry i c))) 1 := by
    unfold digitMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
  have hs : sTopMon K X.p C0 CE1 CE2 X j b = monomial (∑ i : Fin (segS X.TT j),
      if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
            ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i)) +
          Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * b.sg i)
      else 0) 1 := by
    unfold sTopMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
    · simp
  have ha : aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) :
      MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^ symLev X.p C0 CE1 CE2 X j v) (monomial μ c) =
      monomial (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) c := by
    rw [aeval_monomial, monomial_finsupp_sum_index]
    congr 1
    refine Finsupp.prod_congr fun v _ => ?_
    rw [← pow_mul, X_pow_eq_monomial]
  unfold ioBlock ioExp baseExp
  rw [hd, hs, ha, monomial_mul, monomial_mul, one_mul, one_mul]

theorem ioFockAt : IoFockAt := by
  intro C0 CE1 CE2 X K _ hp j b u u'
  let f : MvPolynomial (BV C0 CE1 CE2 X j) K →ₗ[K] MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
    (LinearMap.mulLeft K (digitMon K C0 CE1 CE2 X j b * sTopMon K X.p C0 CE1 CE2 X j b)).comp
      (aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) :
        MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^ symLev X.p C0 CE1 CE2 X j v)).toLinearMap
  exact fock_monoMap f (ioExp C0 CE1 CE2 X j b) (ioExp_inj C0 CE1 CE2 X hp j b)
    (fun μ c => ioBlock_monomial C0 CE1 CE2 X K j b μ c) u u'

end Formalism.MainNotions.ColumnSystems.Pf
