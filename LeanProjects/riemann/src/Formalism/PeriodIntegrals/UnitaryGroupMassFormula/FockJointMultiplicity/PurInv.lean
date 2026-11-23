import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurChain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHW

noncomputable section

open MvPolynomial

namespace PI.FJMB

variable {σ : Type*}

theorem bRow_apply {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b P = ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (b, k)) P := by
  rw [PI.FJM.bRow, LinearMap.sum_apply]; simp

theorem bCol_apply {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (P : MvPolynomial σ ℂ) :
    PI.FJM.bCol ι c d P = ∑ i : Fin m, X (ι (i, c)) * pderiv (ι (i, d)) P := by
  rw [PI.FJM.bCol, LinearMap.sum_apply]; simp

theorem translate_pairs {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq σ] (u w : κ → σ)
    (_hw : Function.Injective w) (huw : ∀ k k', u k ≠ w k') (f : MvPolynomial σ R)
    (h : ∑ k, X (u k) * pderiv (w k) f = 0) {K : Type*} [Field K] [CharZero K] [Algebra R K] (y : σ → K) (t : K) :
    aeval (fun v => y v + t * ∑ k, if w k = v then y (u k) else 0) f = aeval y f := by
  classical
  refine aeval_translate_eq f (Finset.univ.image w) (fun v => ∑ k, if w k = v then X (u k) else 0) ?_ y
    (fun v => ∑ k, if w k = v then y (u k) else 0) ?_ ?_ t
  · calc ∑ v ∈ Finset.univ.image w, (∑ k, if w k = v then (X (u k) : MvPolynomial σ R) else 0) * pderiv v f
        = ∑ k, ∑ v ∈ Finset.univ.image w, if w k = v then X (u k) * pderiv v f else 0 := by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); split_ifs <;> simp
      _ = ∑ k, X (u k) * pderiv (w k) f := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_ite_eq]; simp
      _ = 0 := h
  · intro v hv
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have : w k ≠ v := fun e => hv (by rw [← e]; exact Finset.mem_image_of_mem w (Finset.mem_univ k))
    simp [this]
  · intro v _
    have hz : ∀ k, (∑ k', if w k' = u k then (Polynomial.C (y (u k')) : Polynomial K) else 0) = 0 :=
      fun k => Finset.sum_eq_zero (fun k' _ => by simp [Ne.symm (huw k k')])
    simp only [map_sum, apply_ite (aeval _), aeval_X, map_zero, apply_ite Polynomial.C]
    simp only [hz, mul_zero, add_zero]

def fill {K : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (M : Fin m → Fin n → K) (p : σ → K) : σ → K :=
  Function.extend ι (fun x => M x.1 x.2) p

theorem fill_ι {K : Type*} {m n : ℕ} {ι : Fin m × Fin n → σ} (hι : Function.Injective ι) (M : Fin m → Fin n → K)
    (p : σ → K) (x : Fin m × Fin n) : fill ι M p (ι x) = M x.1 x.2 :=
  hι.extend_apply _ _ _

theorem fill_not {K : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (M : Fin m → Fin n → K)
    (p : σ → K) (v : σ) (hv : ∀ x, ι x ≠ v) : fill ι M p v = p v :=
  Function.extend_apply' _ _ _ (fun ⟨x, hx⟩ => hv x hx)

def rowAddM {K : Type*} [Field K] {m n : ℕ} (M : Fin m → Fin n → K) (a b : Fin m) (t : K) : Fin m → Fin n → K :=
  fun i k => if i = b then M i k + t * M a k else M i k

def colAddM {K : Type*} [Field K] {m n : ℕ} (M : Fin m → Fin n → K) (c d : Fin n) (t : K) : Fin m → Fin n → K :=
  fun i k => if k = d then M i k + t * M i c else M i k

theorem row_inv {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (a b : Fin m) (hab : a ≠ b)
    (f : MvPolynomial σ ℂ) (hf : PI.FJM.bRow ι a b f = 0) {K : Type*} [Field K] [CharZero K] [Algebra ℂ K]
    (M : Fin m → Fin n → K) (p : σ → K) (t : K) :
    aeval (fill ι (rowAddM M a b t) p) f = aeval (fill ι M p) f := by
  classical
  have key := translate_pairs (R := ℂ) (fun k : Fin n => ι (a, k)) (fun k => ι (b, k))
    (fun k k' e => by have := hι e; simp at this; exact this)
    (fun k k' e => hab (by have := hι e; simp at this; exact this.1)) f (by rw [← bRow_apply]; exact hf)
    (fill ι M p) t
  refine Eq.trans ?_ key
  congr 1
  congr 1
  funext v
  by_cases hv : ∃ x, ι x = v
  · obtain ⟨⟨i, k⟩, rfl⟩ := hv
    rw [fill_ι hι, fill_ι hι]
    simp only [rowAddM]
    have hs : (∑ k', if ι (b, k') = ι (i, k) then fill ι M p (ι (a, k')) else 0) = if i = b then M a k else 0 := by
      simp only [hι.eq_iff, Prod.mk.injEq, fill_ι hι]
      by_cases hib : i = b
      · subst hib; simp
      · simp [Ne.symm hib, hib]
    rw [hs]; split_ifs <;> simp
  · push Not at hv
    rw [fill_not _ _ _ _ hv, fill_not _ _ _ _ hv]
    have : (∑ k', if ι (b, k') = v then fill ι M p (ι (a, k')) else 0) = 0 :=
      Finset.sum_eq_zero (fun k' _ => by simp [hv (b, k')])
    rw [this, mul_zero, add_zero]

theorem col_inv {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (c d : Fin n) (hcd : c ≠ d)
    (f : MvPolynomial σ ℂ) (hf : PI.FJM.bCol ι c d f = 0) {K : Type*} [Field K] [CharZero K] [Algebra ℂ K]
    (M : Fin m → Fin n → K) (p : σ → K) (t : K) :
    aeval (fill ι (colAddM M c d t) p) f = aeval (fill ι M p) f := by
  classical
  have key := translate_pairs (R := ℂ) (fun i : Fin m => ι (i, c)) (fun i => ι (i, d))
    (fun i i' e => by have := hι e; simp at this; exact this)
    (fun i i' e => hcd (by have := hι e; simp at this; exact this.2)) f (by rw [← bCol_apply]; exact hf)
    (fill ι M p) t
  refine Eq.trans ?_ key
  congr 1
  congr 1
  funext v
  by_cases hv : ∃ x, ι x = v
  · obtain ⟨⟨i, k⟩, rfl⟩ := hv
    rw [fill_ι hι, fill_ι hι]
    simp only [colAddM]
    have hs : (∑ i', if ι (i', d) = ι (i, k) then fill ι M p (ι (i', c)) else 0) = if k = d then M i c else 0 := by
      simp only [hι.eq_iff, Prod.mk.injEq, fill_ι hι]
      by_cases hkd : k = d
      · subst hkd; simp
      · simp [Ne.symm hkd, hkd]
    rw [hs]; split_ifs <;> simp
  · push Not at hv
    rw [fill_not _ _ _ _ hv, fill_not _ _ _ _ hv]
    have : (∑ i', if ι (i', d) = v then fill ι M p (ι (i', c)) else 0) = 0 :=
      Finset.sum_eq_zero (fun i' _ => by simp [hv (i', d)])
    rw [this, mul_zero, add_zero]

end PI.FJMB
