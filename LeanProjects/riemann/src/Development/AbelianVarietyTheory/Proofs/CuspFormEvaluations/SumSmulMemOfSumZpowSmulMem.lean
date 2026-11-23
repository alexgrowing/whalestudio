import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan

open MvPolynomial Matrix

namespace GlobalTheory.Harm

section General

variable {K V ι : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

theorem sum_smul_mem_of_sum_pow_smul_mem (W : Submodule K V) (S : Finset ι) (e : ι → ℕ) (v : ι → V)
    (h : ∀ u : K, u ≠ 0 → ∑ i ∈ S, u ^ e i • v i ∈ W) (f : ℕ → K) :
    ∑ i ∈ S, f (e i) • v i ∈ W := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  have hP : (∑ i ∈ S, Polynomial.monomial (e i) (φ (v i))) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := {0}ᶜ) ?_ (Set.finite_singleton (0 : K)).infinite_compl
    intro u hu
    have := hφ _ (h u hu)
    simp only [map_sum, map_smul, smul_eq_mul] at this
    simpa [Polynomial.eval_finset_sum, mul_comm] using this
  have := congrArg (Polynomial.lsum (R := K) (fun n => f n • (LinearMap.id : K →ₗ[K] K))) hP
  simpa [map_sum, Polynomial.lsum_apply, Polynomial.sum_monomial_index] using this

theorem sum_smul_mem_of_sum_zpow_smul_mem (W : Submodule K V) (S : Finset ι) (e : ι → ℤ) (v : ι → V)
    (h : ∀ u : K, u ≠ 0 → ∑ i ∈ S, u ^ e i • v i ∈ W) (f : ℤ → K) :
    ∑ i ∈ S, f (e i) • v i ∈ W := by
  set N : ℕ := ∑ i ∈ S, (e i).natAbs with hN
  have hle : ∀ i ∈ S, (((e i + N).toNat : ℕ) : ℤ) = e i + N := fun i hi => by
    have : (e i).natAbs ≤ N :=
      Finset.single_le_sum (f := fun i => (e i).natAbs) (fun _ _ => Nat.zero_le _) hi
    omega
  have := sum_smul_mem_of_sum_pow_smul_mem W S (fun i => (e i + N).toNat) v (fun u hu => by
    have := W.smul_mem (u ^ N) (h u hu)
    rw [Finset.smul_sum] at this
    convert this using 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [smul_smul, ← zpow_natCast, hle i hi, zpow_add₀ hu, zpow_natCast, mul_comm])
    (fun n => f (n - N))
  convert this using 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hle i hi, add_sub_cancel_right]

theorem derivation_mem_of_aeval_mem {σ : Type*} (W : Submodule K (MvPolynomial σ K))
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (w : MvPolynomial σ K)
    (h : ∀ s : K, aeval (fun v => X v + s • D (X v)) w ∈ W) : D w ∈ W := by
  classical
  let Φ : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
    aeval fun v => Polynomial.C (X v) + Polynomial.X * Polynomial.C (D (X v))
  have hev (s : K) (P : MvPolynomial σ K) :
      (Φ P).eval (C s) = aeval (fun v => X v + s • D (X v)) P := by
    induction P using MvPolynomial.induction_on with
    | C r => simp [Φ, algHom_C]
    | add P Q hP hQ => simp only [map_add, Polynomial.eval_add, hP, hQ]
    | mul_X P v hP =>
      rw [map_mul, map_mul, Polynomial.eval_mul, hP]
      simp only [Φ, aeval_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, smul_eq_C_mul]
  have hco (P : MvPolynomial σ K) : (Φ P).coeff 0 = P ∧ (Φ P).coeff 1 = D P := by
    induction P using MvPolynomial.induction_on with
    | C r => simp [Φ, algHom_C, Polynomial.coeff_C]
    | add P Q hP hQ => simp only [map_add, Polynomial.coeff_add, hP, hQ, and_self]
    | mul_X P v hP =>
      have e : Φ (P * X v) = Φ P * Polynomial.C (X v) +
          Polynomial.X * (Φ P * Polynomial.C (D (X v))) := by
        rw [map_mul]; simp only [Φ, aeval_X]; ring
      rw [e]
      obtain ⟨h0, h1⟩ := hP
      constructor
      · rw [Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_X_mul_zero, h0, add_zero]
      · rw [Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_X_mul,
          Polynomial.coeff_mul_C, h0, h1, Derivation.leibniz]
        simp only [smul_eq_mul]; ring
  have := sum_smul_mem_of_sum_pow_smul_mem W (Φ w).support id (Φ w).coeff (fun u _ => by
    have := h u
    rw [← hev, Polynomial.eval_eq_sum, Polynomial.sum_def] at this
    simpa [smul_eq_C_mul, mul_comm] using this) (fun n => if n = 1 then 1 else 0)
  rw [← (hco w).2]
  by_cases h1 : 1 ∈ (Φ w).support
  · simpa [ite_smul, h1] using this
  · rw [Polynomial.notMem_support_iff.mp h1]; exact W.zero_mem

end General

variable {R : Type*} [CommRing R] {T : Type*} {p q : ℕ} {κ : Type*}

variable (R p q) in

noncomputable def colDer (t : T) (k l : κ) : Derivation R (Poly R T p q κ) (Poly R T p q κ) :=
  ∑ a : Fin p, (X (xVar t a k) : Poly R T p q κ) • pderiv (xVar t a l) -
    ∑ b : Fin q, (X (yVar t b l) : Poly R T p q κ) • pderiv (yVar t b k)

variable (R p q) in

noncomputable def colLie (t : T) (k l : κ) : Module.End R (Poly R T p q κ) :=
  (colDer R p q t k l).toLinearMap

theorem colDer_apply (t : T) (k l : κ) (P : Poly R T p q κ) :
    colDer R p q t k l P = ∑ a, X (xVar t a k) * pderiv (xVar t a l) P -
      ∑ b, X (yVar t b l) * pderiv (yVar t b k) P := by
  have h {ι : Type} (S : Finset ι) (D : ι → Derivation R (Poly R T p q κ) (Poly R T p q κ)) :
      (∑ i ∈ S, D i) P = ∑ i ∈ S, D i P := by
    rw [← Finset.sum_apply]
    exact congrFun (map_sum Derivation.coeFnAddMonoidHom D S) P
  simp [colDer, h]

theorem colLie_apply (t : T) (k l : κ) (P : Poly R T p q κ) :
    colLie R p q t k l P = ∑ a, X (xVar t a k) * pderiv (xVar t a l) P -
      ∑ b, X (yVar t b l) * pderiv (yVar t b k) P := colDer_apply t k l P

theorem colDer_X_xVar [DecidableEq T] [DecidableEq κ] (t t' : T) (k l j : κ) (a : Fin p) :
    colDer R p q t k l (X (xVar t' a j)) = if t' = t ∧ j = l then X (xVar t a k) else 0 := by
  rw [colDer_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [pderiv_X, Pi.single_apply]
  · have (a' : Fin p) : (xVar t' a j : Var T p q κ) ≠ xVar t a' l := by
      intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.2⟩
    simp [pderiv_X, Pi.single_apply, this]

theorem colDer_X_yVar [DecidableEq T] [DecidableEq κ] (t t' : T) (k l j : κ) (b : Fin q) :
    colDer R p q t k l (X (yVar t' b j)) = if t' = t ∧ j = k then -X (yVar t b l) else 0 := by
  rw [colDer_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [pderiv_X, Pi.single_apply]
  · have (b' : Fin q) : (yVar t' b j : Var T p q κ) ≠ yVar t b' k := by
      intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.2⟩
    simp [pderiv_X, Pi.single_apply, this]

def colWeight (m : Var T p q κ →₀ ℕ) (t : T) (k : κ) : ℤ :=
  ∑ a, (m (xVar t a k) : ℤ) - ∑ b, (m (yVar t b k) : ℤ)

theorem colWeight_add (m m' : Var T p q κ →₀ ℕ) (t : T) (k : κ) :
    colWeight (m + m') t k = colWeight m t k + colWeight m' t k := by
  simp only [colWeight, Finsupp.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring

theorem colWeight_single_xVar [DecidableEq T] [DecidableEq κ] (t t' : T) (a : Fin p) (k j : κ) :
    colWeight (Finsupp.single (xVar t' a j : Var T p q κ) 1) t k =
      if t' = t ∧ j = k then 1 else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [colWeight, Finsupp.single_apply]
  · have (a' : Fin p) : (xVar t' a j : Var T p q κ) ≠ xVar t a' k := by
      intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.2⟩
    simp [colWeight, Finsupp.single_apply, this]

theorem colWeight_single_yVar [DecidableEq T] [DecidableEq κ] (t t' : T) (b : Fin q) (k j : κ) :
    colWeight (Finsupp.single (yVar t' b j : Var T p q κ) 1) t k =
      if t' = t ∧ j = k then -1 else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [colWeight, Finsupp.single_apply]
  · have (b' : Fin q) : (yVar t' b j : Var T p q κ) ≠ yVar t b' k := by
      intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.2⟩
    simp [colWeight, Finsupp.single_apply, this]

theorem colLie_monomial (t : T) (k : κ) (m : Var T p q κ →₀ ℕ) (c : R) :
    colLie R p q t k k (monomial m c) = (colWeight m t k : R) • monomial m c := by
  simp only [colLie_apply, X_mul_pderiv_monomial, colWeight, Int.cast_sub, Int.cast_sum,
    Int.cast_natCast, sub_smul, Finset.sum_smul, Nat.cast_smul_eq_nsmul]

variable (R T p q κ) in

theorem iSup_iInf_eigenspace_colLie :
    ⨆ μ : T → κ → ℤ, (⨅ t, ⨅ k, Module.End.eigenspace (colLie R p q t k k) (μ t k : R)) = ⊤ := by
  rw [eq_top_iff]
  intro P _
  rw [P.as_sum]
  refine Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem (colWeight m) ?_
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, colLie_monomial, implies_true]

theorem colLie_diag_comm [DecidableEq T] [DecidableEq κ] (t t' : T) (i k l : κ) :
    colLie R p q t i i * colLie R p q t' k l - colLie R p q t' k l * colLie R p q t i i =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : R) else 0) •
        colLie R p q t' k l := by
  have : ⁅colDer R p q t i i, colDer R p q t' k l⁆ =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : R) else 0) •
        colDer R p q t' k l := by
    refine MvPolynomial.derivation_ext fun ⟨s, r, j⟩ => ?_
    rw [Derivation.commutator_apply, Derivation.smul_apply]
    rcases r with a | b
    · simp only [colDer_X_xVar, apply_ite (colDer R p q t i i), apply_ite (colDer R p q t' k l),
        map_zero]
      by_cases h1 : s = t' ∧ j = l
      · obtain ⟨rfl, rfl⟩ := h1
        by_cases h2 : s = t
        · subst h2
          by_cases h3 : i = k <;> by_cases h4 : i = j <;> simp [h3, h4, eq_comm, sub_smul] <;>
            (try split_ifs) <;> simp_all
        · simp [h2, Ne.symm h2]
      · simp only [if_neg h1, smul_zero, zero_sub, neg_eq_zero]
        split_ifs with h2 h3
        · exact absurd ⟨h2.1.trans h3.1, h2.2.trans h3.2⟩ h1
        · rfl
        · rfl
    · simp only [colDer_X_yVar, apply_ite (colDer R p q t i i), apply_ite (colDer R p q t' k l),
        map_zero, map_neg]
      by_cases h1 : s = t' ∧ j = k
      · obtain ⟨rfl, rfl⟩ := h1
        by_cases h2 : s = t
        · subst h2
          by_cases h3 : i = l <;> by_cases h4 : i = j <;> simp [h3, h4, eq_comm, sub_smul] <;>
            (try split_ifs) <;> simp_all
        · simp [h2, Ne.symm h2]
      · simp only [if_neg h1, smul_zero, zero_sub, neg_eq_zero]
        split_ifs with h2 h3
        · exact absurd ⟨h2.1.trans h3.1, h2.2.trans h3.2⟩ h1
        · simp
        · rfl
  refine LinearMap.ext fun P => ?_
  have := DFunLike.congr_fun this P
  rw [Derivation.commutator_apply] at this
  exact this

section Stable

variable [Fintype κ] [DecidableEq κ] [DecidableEq T]

theorem exists_colAct_eq_aeval (t : T) {k l : κ} (hkl : k ≠ l) (s : R) :
    ∃ g : T → GL κ R, ∀ P : Poly R T p q κ,
      colAct R T p q κ g P = aeval (fun v => X v + s • colDer R p q t k l (X v)) P := by
  let g₀ : GL κ R := ⟨transvection l k (-s), transvection l k s,
    by rw [transvection_mul_transvection_same _ _ hkl.symm, neg_add_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same _ _ hkl.symm, add_neg_cancel, transvection_zero]⟩
  refine ⟨Pi.mulSingle t g₀, fun P => ?_⟩
  rw [colAct_apply]
  refine DFunLike.congr_fun (MvPolynomial.algHom_ext fun ⟨t', r, j⟩ => ?_) P
  rcases r with a | b
  · rw [colSubst_X_xVar, aeval_X, colDer_X_xVar]
    by_cases ht : t' = t
    · subst ht
      have : (((Pi.mulSingle t' g₀ : T → GL κ R) t')⁻¹ : GL κ R).val j =
          Pi.single j 1 + (if j = l then s else 0) • Pi.single k 1 := by
        ext i
        simp [g₀, transvection, Matrix.one_apply, Matrix.single_apply, Pi.single_apply, eq_comm, ite_and]
        split_ifs <;> simp_all
      rw [this, map_add, map_smul, xForm_single, xForm_single]
      by_cases hj : j = l <;> simp [hj]
    · have : (((Pi.mulSingle t g₀ : T → GL κ R) t')⁻¹ : GL κ R).val j = Pi.single j 1 := by
        ext i
        simp [Pi.mulSingle_eq_of_ne ht, Matrix.one_apply, Pi.single_apply, eq_comm]
      rw [this, xForm_single]; simp [ht]
  · rw [colSubst_X_yVar, aeval_X, colDer_X_yVar]
    by_cases ht : t' = t
    · subst ht
      have : (fun i => (((Pi.mulSingle t' g₀ : T → GL κ R) t') : GL κ R).val i j) =
          Pi.single j 1 + (if j = k then -s else 0) • Pi.single l 1 := by
        ext i
        simp [g₀, transvection, Matrix.one_apply, Matrix.single_apply, Pi.single_apply, eq_comm, ite_and]
        split_ifs <;> simp_all
      rw [this, map_add, map_smul, yForm_single, yForm_single]
      by_cases hj : j = k <;> simp [hj]
    · have : (fun i => (((Pi.mulSingle t g₀ : T → GL κ R) t') : GL κ R).val i j) = Pi.single j 1 := by
        ext i
        simp [Pi.mulSingle_eq_of_ne ht, Matrix.one_apply, Pi.single_apply, eq_comm]
      rw [this, yForm_single]; simp [ht]

theorem exists_colAct_monomial (t : T) (k : κ) (u : Rˣ) :
    ∃ g : T → GL κ R, ∀ (m : Var T p q κ →₀ ℕ) (c : R),
      colAct R T p q κ g (monomial m c) = ((u ^ colWeight m t k : Rˣ) : R) • monomial m c := by
  let g₀ : GL κ R := ⟨diagonal (Function.update 1 k ↑u⁻¹), diagonal (Function.update 1 k ↑u),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i
      by_cases h : i = k <;> simp [h],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i
      by_cases h : i = k <;> simp [h]⟩
  refine ⟨Pi.mulSingle t g₀, ?_⟩
  have hX (v : Var T p q κ) : colAct R T p q κ (Pi.mulSingle t g₀) (X v) =
      ((u ^ colWeight (Finsupp.single v 1) t k : Rˣ) : R) • X v := by
    obtain ⟨t', a | b, j⟩ := v
    · rw [colAct_apply, colSubst_X_xVar, ← xForm_single, ← map_smul, colWeight_single_xVar]
      congr 1; ext i
      by_cases ht : t' = t
      · subst ht
        by_cases hj : j = k <;> by_cases hi : j = i <;>
          simp [g₀, diagonal_apply, Pi.single_apply, hj, hi, eq_comm] <;> simp_all [eq_comm]
      · simp [Pi.mulSingle_eq_of_ne ht, Matrix.one_apply, Pi.single_apply, eq_comm, Ne.symm ht]
    · rw [colAct_apply, colSubst_X_yVar, ← yForm_single, ← map_smul, colWeight_single_yVar]
      congr 1; ext i
      by_cases ht : t' = t
      · subst ht
        by_cases hj : j = k <;> by_cases hi : j = i <;>
          simp [g₀, diagonal_apply, Pi.single_apply, hj, hi, eq_comm] <;> simp_all [eq_comm]
      · simp [Pi.mulSingle_eq_of_ne ht, Matrix.one_apply, Pi.single_apply, eq_comm, Ne.symm ht]
  have hpow (v : Var T p q κ) (e : ℕ) :
      colAct R T p q κ (Pi.mulSingle t g₀) (monomial (Finsupp.single v e) 1) =
        ((u ^ colWeight (Finsupp.single v e) t k : Rˣ) : R) • monomial (Finsupp.single v e) 1 := by
    induction e with
    | zero => simp [colWeight]
    | succ e ih =>
      rw [Finsupp.single_add, colWeight_add, monomial_add_single, pow_one, map_mul, ih, hX,
        _root_.zpow_add, Units.val_mul, smul_mul_smul_comm]
  have hm (m : Var T p q κ →₀ ℕ) : colAct R T p q κ (Pi.mulSingle t g₀) (monomial m 1) =
        ((u ^ colWeight m t k : Rˣ) : R) • monomial m 1 := by
    induction m using Finsupp.induction_linear with
    | zero => simp [colWeight]
    | add m m' h h' =>
      have e : (monomial (m + m') 1 : Poly R T p q κ) = monomial m 1 * monomial m' 1 := by
        rw [monomial_mul, mul_one]
      rw [e, map_mul, h, h', colWeight_add, _root_.zpow_add, Units.val_mul, smul_mul_smul_comm]
    | single v e => exact hpow v e
  intro m c
  have e : (monomial m c : Poly R T p q κ) = c • monomial m 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, hm, smul_comm]

end Stable

theorem colLie_mem_of_colAct_mem {K : Type*} [Field K] [Infinite K] [Fintype κ] [DecidableEq κ]
    (W : Submodule K (Poly K T p q κ))
    (hW : ∀ g : T → GL κ K, ∀ w ∈ W, colAct K T p q κ g w ∈ W)
    (t : T) (k l : κ) {w : Poly K T p q κ} (hw : w ∈ W) : colLie K p q t k l w ∈ W := by
  classical
  by_cases hkl : k = l
  · subst hkl
    have := sum_smul_mem_of_sum_zpow_smul_mem W w.support (fun m => colWeight m t k)
      (fun m => monomial m (coeff m w)) (fun u hu => by
        obtain ⟨g, hg⟩ := exists_colAct_monomial (p := p) (q := q) t k (Units.mk0 u hu)
        have := hW g w hw
        rw [w.as_sum, map_sum] at this
        simpa only [hg, Units.val_zpow_eq_zpow_val, Units.val_mk0] using this) Int.cast
    rw [w.as_sum, map_sum]
    simpa only [colLie_monomial] using this
  · refine derivation_mem_of_aeval_mem W (colDer K p q t k l) w fun s => ?_
    obtain ⟨g, hg⟩ := exists_colAct_eq_aeval (p := p) (q := q) t hkl s
    rw [← hg]
    exact hW g w hw

theorem colLie_mem_orbitSpan {K : Type*} [Field K] [Infinite K] [Fintype T] {n : ℕ} (h : p + q ≤ n)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (t : T) (k l : Fin n) {w : Poly K T p q (Fin n)}
    (hw : w ∈ orbitSpan K h c c') : colLie K p q t k l w ∈ orbitSpan K h c c' :=
  colLie_mem_of_colAct_mem _ (fun g _ hP => colAct_mem_orbitSpan h c c' g hP) t k l hw

end GlobalTheory.Harm
