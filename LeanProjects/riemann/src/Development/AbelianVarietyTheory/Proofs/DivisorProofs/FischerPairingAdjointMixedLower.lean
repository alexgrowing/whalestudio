import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.SDown

theorem pderiv_aeval_sum {σ δ : Type} [Fintype σ] [DecidableEq σ] (f : σ → MvPolynomial δ ℂ) (i : δ)
    (G : MvPolynomial σ ℂ) : pderiv i (aeval f G) = ∑ u, pderiv i (f u) * aeval f (pderiv u G) := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, aeval_X, hp, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single k]
      · simp [mul_comm]
      · intro b _ hb
        rw [pderiv_X_of_ne hb.symm]; simp
      · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem derivation_finset_prod {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι]
    (D : Derivation R A A) (f : ι → A) (s : Finset ι) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.prod_insert ha,
      Function.update_self]
    have h1 : ∏ j ∈ s, Function.update f a (D (f a)) j = ∏ j ∈ s, f j := by
      refine Finset.prod_congr rfl fun j hj => ?_
      exact Function.update_of_ne (by rintro rfl; exact ha hj) _ _
    have h2 : ∀ i ∈ s, ∏ j ∈ insert a s, Function.update f i (D (f i)) j =
        f a * ∏ j ∈ s, Function.update f i (D (f i)) j := by
      intro i hi
      rw [Finset.prod_insert ha, Function.update_of_ne (by rintro rfl; exact ha hi)]
    rw [h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, smul_eq_mul, smul_eq_mul]
    ring

theorem derivation_det {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateRow i fun j => D (M i j)).det := by
  have key : ∀ B : Matrix n n A, B.det = ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, B i (σ i) := by
    intro B
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  rw [key, map_sum]
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, derivation_finset_prod, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Units.smul_def]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    simp [Matrix.updateRow_self]
  · rw [Function.update_of_ne hj, Matrix.updateRow_ne hj]

theorem derivation_sum_apply {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} (s : Finset ι)
    (D : ι → Derivation R A A) (x : A) : (∑ t ∈ s, D t) x = ∑ t ∈ s, D t x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

variable {P Q S : ℕ}

theorem pderiv_u_mS (a : Fin P) (c : Fin S) (a0 : Fin P) (b0 : Fin Q) :
    pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (mS P Q S a0 b0) =
      if a0 = a then X (Sum.inr b0, Sum.inr c) else 0 := by
  classical
  simp [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem pderiv_t_mS (b : Fin Q) (c : Fin S) (a0 : Fin P) (b0 : Fin Q) :
    pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (mS P Q S a0 b0) =
      if b0 = b then X (Sum.inl a0, Sum.inr c) else 0 := by
  classical
  simp [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem pderiv_u_detS (h : Q ≤ S) (a : Fin P) (c : Fin S) :
    pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (detS P Q S h) = 0 := by
  classical
  rw [detS, derivation_det]
  refine Finset.sum_eq_zero fun i _ => Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
  simp [pderiv_X, Pi.single_apply]

theorem sum_X_pderiv_detS (h : Q ≤ S) (b b' : Fin Q) :
    ∑ c : Fin S, X ((Sum.inr b', Sum.inr c) : Ln P Q 0 S) * pderiv (Sum.inr b, Sum.inr c) (detS P Q S h) =
      if b' = b then detS P Q S h else 0 := by
  classical
  let Dd : Derivation ℂ (Pol P Q 0 S) (Pol P Q 0 S) :=
    ∑ c : Fin S, (X (Sum.inr b', Sum.inr c) : Pol P Q 0 S) • pderiv (Sum.inr b, Sum.inr c)
  have hD : ∀ p, Dd p = ∑ c : Fin S, X ((Sum.inr b', Sum.inr c) : Ln P Q 0 S) * pderiv (Sum.inr b, Sum.inr c) p := by
    intro p; simp only [Dd, derivation_sum_apply, Derivation.smul_apply, smul_eq_mul]
  rw [← hD, detS, derivation_det]
  have hrow : ∀ i j : Fin Q, Dd ((Matrix.of fun b c : Fin Q => (X (Sum.inr b, Sum.inr (Fin.castLE h c)) : Pol P Q 0 S)) i j) =
      if i = b then X (Sum.inr b', Sum.inr (Fin.castLE h j)) else 0 := by
    intro i j
    rw [hD]
    by_cases hi : i = b
    · subst hi; simp [pderiv_X, Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp [pderiv_X, Pi.single_apply, hi]
  simp_rw [hrow]
  rw [Finset.sum_eq_single b]
  · simp only [if_true]
    split_ifs with hb
    · subst hb
      congr 1
      ext i j
      by_cases hi : i = b' <;> simp [Matrix.updateRow_apply, hi]
    · refine Matrix.det_zero_of_row_eq hb ?_
      ext j
      simp [Matrix.updateRow_apply, Ne.symm hb]
  · intro i _ hi
    refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    simp [hi]
  · simp

end GlobalTheory.CharPair.SDown

namespace GlobalTheory.CharPair.SDown

variable {P Q S : ℕ}

theorem pderiv_u_aeval (a : Fin P) (c : Fin S) (H : Mdl P Q) :
    pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) H) =
      ∑ b0 : Fin Q, X (Sum.inr b0, Sum.inr c) * aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a, b0) H) := by
  classical
  rw [pderiv_aeval_sum, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [pderiv_u_mS]
  · intro a0 _ ha0; simp [pderiv_u_mS, ha0]
  · simp

theorem pderiv_t_aeval (b : Fin Q) (c : Fin S) (H : Mdl P Q) :
    pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) H) =
      ∑ a0 : Fin P, X (Sum.inl a0, Sum.inr c) * aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a0, b) H) := by
  classical
  rw [pderiv_aeval_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a0 _ => ?_
  rw [Finset.sum_eq_single b]
  · simp [pderiv_t_mS]
  · intro b0 _ hb0; simp [pderiv_t_mS, hb0]
  · simp

end GlobalTheory.CharPair.SDown

namespace GlobalTheory.CharPair.SDown

variable {P Q S : ℕ}

theorem rhs_eq (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inl a) G) =
      (∑ a0 : Fin P, ∑ b0 : Fin Q, mS P Q S a0 b0 *
          aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a0, b) (pderiv (a, b0) G)) +
        ((S + k' : ℕ) : ℂ) • aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a, b) G)) *
        detS P Q S h ^ k' := by
  simp [embS, opS, mulM, derM, LinearMap.sum_apply, map_sum, Module.End.mul_apply]

theorem key (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin S, pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (pderiv (Sum.inl a, Sum.inr c) (embS P Q S h k' G)) =
      embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inl a) G) := by
  classical
  rw [rhs_eq]
  set m : Fin P × Fin Q → Pol P Q 0 S := fun ab => mS P Q S ab.1 ab.2 with hm
  set D := detS P Q S h with hDdef
  have hE : embS P Q S h k' G = aeval m G * D ^ k' := by simp [embS, hm, hDdef]
  have step1 : ∀ c : Fin S, pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (embS P Q S h k' G) =
      ∑ b0 : Fin Q, X (Sum.inr b0, Sum.inr c) * aeval m (pderiv (a, b0) G) * D ^ k' := by
    intro c
    rw [hE, Derivation.leibniz, Derivation.leibniz_pow, hDdef, pderiv_u_detS, hm, pderiv_u_aeval]
    simp only [mul_zero, smul_zero, zero_add, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b0 _ => ?_
    ring
  have step2 : ∀ (c : Fin S) (b0 : Fin Q),
      pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (X (Sum.inr b0, Sum.inr c) * aeval m (pderiv (a, b0) G) * D ^ k') =
        (if b0 = b then aeval m (pderiv (a, b) G) * D ^ k' else 0) +
        X (Sum.inr b0, Sum.inr c) * (∑ a0 : Fin P, X (Sum.inl a0, Sum.inr c) *
            aeval m (pderiv (a0, b) (pderiv (a, b0) G))) * D ^ k' +
        aeval m (pderiv (a, b0) G) * ((k' : Pol P Q 0 S) * D ^ (k' - 1)) *
          (X (Sum.inr b0, Sum.inr c) * pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) D) := by
    intro c b0
    rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, hm, pderiv_t_aeval, pderiv_X, Pi.single_apply]
    simp only [smul_eq_mul, nsmul_eq_mul, Prod.mk.injEq, Sum.inr.injEq, and_true]
    by_cases hb : b0 = b
    · subst hb
      simp only [if_true]
      ring
    · simp only [hb, if_false]
      ring
  have hT1 : ∑ c : Fin S, ∑ b0 : Fin Q, X ((Sum.inr b0, Sum.inr c) : Ln P Q 0 S) * (∑ a0 : Fin P, X (Sum.inl a0, Sum.inr c) *
      aeval m (pderiv (a0, b) (pderiv (a, b0) G))) * D ^ k' =
      ∑ a0 : Fin P, ∑ b0 : Fin Q, mS P Q S a0 b0 * aeval m (pderiv (a0, b) (pderiv (a, b0) G)) * D ^ k' := by
    simp only [mS, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b0 _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a0 _ => Finset.sum_congr rfl fun c _ => by ring
  have hT3 : ∑ c : Fin S, ∑ b0 : Fin Q, aeval m (pderiv (a, b0) G) * ((k' : Pol P Q 0 S) * D ^ (k' - 1)) *
      (X ((Sum.inr b0, Sum.inr c) : Ln P Q 0 S) * pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) D) =
      (k' : Pol P Q 0 S) * aeval m (pderiv (a, b) G) * D ^ k' := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have e : ∀ b0 : Fin Q, ∑ c : Fin S, X ((Sum.inr b0, Sum.inr c) : Ln P Q 0 S) * pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) D =
        if b0 = b then D else 0 := fun b0 => by rw [hDdef]; exact sum_X_pderiv_detS h b b0
    simp only [e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases k' with _ | k
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]; ring
  have hT0 : ∑ c : Fin S, ∑ b0 : Fin Q, (if b0 = b then aeval m (pderiv (a, b) G) * D ^ k' else 0) =
      (S : Pol P Q 0 S) * aeval m (pderiv (a, b) G) * D ^ k' := by
    simp [Finset.sum_ite_eq', mul_assoc]
  simp_rw [step1, map_sum, step2, Finset.sum_add_distrib]
  rw [hT0, hT1, hT3, Nat.cast_smul_eq_nsmul ℂ, nsmul_eq_mul, add_mul, Finset.sum_mul]
  simp only [Finset.sum_mul]
  push_cast
  ring

end GlobalTheory.CharPair.SDown

namespace GlobalTheory.CharPair

theorem fockAct1_Eab_inr_inl_embS_pair : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q)
    (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inr b) (Sum.inl a)) f)
      (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inl a) G)) := by
  intro P Q S h k' a b G f
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
  have hterm : ∀ c : Fin S, omE ((Sum.inr b : Ix P Q), (Sum.inr c : Ix 0 S)) (Sum.inl a, Sum.inr c) f =
      (f * X (Sum.inr b, Sum.inr c)) * X (Sum.inl a, Sum.inr c) := by
    intro c
    simp [omE, raiB, lowB, linePos]
    ring
  simp only [hterm, map_sum, LinearMap.sum_apply, GlobalTheory.DefLift.BilFischer.pair_mul_X]
  rw [← map_sum]
  exact congrArg _ (SDown.key h k' a b G)

end GlobalTheory.CharPair
