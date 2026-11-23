import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.DeltaEqGdelta

open MvPolynomial

namespace PI.WickFormula.Asm

def xdeg {r s : ℕ} (m : Fin r ⊕ Fin s →₀ ℕ) : ℕ := ∑ i, m (Sum.inl i)

theorem xdeg_add {r s : ℕ} (u v : Fin r ⊕ Fin s →₀ ℕ) : xdeg (u + v) = xdeg u + xdeg v := by
  simp [xdeg, Finset.sum_add_distrib]

theorem xdeg_single {r s : ℕ} (i : Fin r) : xdeg (Finsupp.single (Sum.inl i : Fin r ⊕ Fin s) 1) = 1 := by
  simp [xdeg, Finsupp.single_apply]

theorem xdeg_le_totalDegree {k : Type} [CommRing k] {r s : ℕ} (P : MvPolynomial (Fin r ⊕ Fin s) k)
    (m : Fin r ⊕ Fin s →₀ ℕ) (hm : m ∈ P.support) : xdeg m ≤ P.totalDegree := by
  have h := MvPolynomial.le_totalDegree hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sum_type] at h
  unfold xdeg
  omega

theorem dL_monomial_support {k : Type} [CommRing k] {r s : ℕ} (κ : Fin r → Fin s → k) (i : Fin r)
    (m : Fin r ⊕ Fin s →₀ ℕ) (c : k) (u : Fin r ⊕ Fin s →₀ ℕ)
    (hu : u ∈ (Gen.dL κ i (monomial m c)).support) : xdeg u ≤ xdeg m := by
  have key : Gen.dL κ i (monomial m c) =
      ∑ j, monomial (m - Finsupp.single (Sum.inr j) 1) (κ i j * (c * (m (Sum.inr j) : k))) := by
    simp [Gen.dL, pderiv_monomial, smul_monomial]
  rw [key] at hu
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hu)
  have hu' := MvPolynomial.support_monomial_subset hj
  rw [Finset.mem_singleton] at hu'
  subst hu'
  unfold xdeg
  exact Finset.sum_le_sum fun i _ => by simp

section
variable {k AA M : Type} [CommRing k] [Algebra ℚ k] [Ring AA] [Algebra k AA] [AddCommGroup M]
  [Module AA M] {r s : ℕ}

theorem ordEval_add (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) (P Q : MvPolynomial (Fin r ⊕ Fin s) k) :
    ordEval a a' (P + Q) = ordEval a a' P + ordEval a a' Q := by
  obtain ⟨f, hf⟩ := h1 k AA r s a a'
  rw [← hf, ← hf, ← hf, map_add]

theorem ordEval_zero (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) :
    ordEval a a' (0 : MvPolynomial (Fin r ⊕ Fin s) k) = 0 := by
  obtain ⟨f, hf⟩ := h1 k AA r s a a'
  rw [← hf, map_zero]

noncomputable def phiH (h1 : OrdLin) (a b : Fin r → AA) (a' b' : Fin s → AA) (σ₀ : M) :
    MvPolynomial (Fin r ⊕ Fin s) k →+ M :=
  AddMonoidHom.mk' (fun R => ordEval (a + b) (a' + b') R • σ₀)
    (fun P Q => by rw [ordEval_add h1, add_smul])

theorem phiH_apply (h1 : OrdLin) (a b : Fin r → AA) (a' b' : Fin s → AA) (σ₀ : M)
    (R : MvPolynomial (Fin r ⊕ Fin s) k) : phiH h1 a b a' b' σ₀ R = ordEval (a + b) (a' + b') R • σ₀ := rfl

noncomputable def tH (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) (κ : Fin r → Fin s → k) (σ₀ : M)
    (n : ℕ) : MvPolynomial (Fin r ⊕ Fin s) k →+ M :=
  AddMonoidHom.mk' (fun R => ordEval a a' ((n.factorial : ℚ)⁻¹ • (delta κ ^ n) R) • σ₀)
    (fun P Q => by rw [map_add, smul_add, ordEval_add h1, add_smul])

theorem tH_apply (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) (κ : Fin r → Fin s → k) (σ₀ : M)
    (n : ℕ) (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    tH h1 a a' κ σ₀ n R = ordEval a a' ((n.factorial : ℚ)⁻¹ • (delta κ ^ n) R) • σ₀ := rfl

noncomputable def psi (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) (κ : Fin r → Fin s → k) (σ₀ : M)
    (N : ℕ) (R : MvPolynomial (Fin r ⊕ Fin s) k) : M :=
  ∑ n ∈ Finset.range N, tH h1 a a' κ σ₀ n R

theorem psi_sum (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) (κ : Fin r → Fin s → k) (σ₀ : M)
    (N : ℕ) {α : Type} (t : Finset α) (g : α → MvPolynomial (Fin r ⊕ Fin s) k) :
    psi h1 a a' κ σ₀ N (∑ x ∈ t, g x) = ∑ x ∈ t, psi h1 a a' κ σ₀ N (g x) := by
  unfold psi
  simp only [map_sum]
  exact Finset.sum_comm

theorem factorial_smul (n : ℕ) (S : MvPolynomial (Fin r ⊕ Fin s) k) :
    (((n + 1).factorial : ℚ)⁻¹ • ((n + 1) • S)) = ((n.factorial : ℚ)⁻¹ • S) := by
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp

variable {a b : Fin r → AA} {a' b' : Fin s → AA} {κ : Fin r → Fin s → k} {σ₀ : M}

theorem phi_X (h1 : OrdLin) (h2 : OrdX) (h4 : BComm) (H : Hyp a b a' b' κ σ₀) (i : Fin r)
    (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    phiH h1 a b a' b' σ₀ (X (Sum.inl i) * R) =
      a i • phiH h1 a b a' b' σ₀ R + phiH h1 a b a' b' σ₀ (Gen.dL κ i R) := by
  have hc : ∀ i i', Commute ((a + b) i) ((a + b) i') := by
    intro i i'
    simp only [Pi.add_apply]
    exact ((H.h1 i i').1.add_right (H.h1 i i').2.1).add_left
      (((H.h1 i' i).2.1.symm).add_right (H.h1 i i').2.2)
  simp only [phiH_apply]
  rw [h2 k AA r s (a + b) (a' + b') hc i R, Pi.add_apply, add_mul, add_smul, mul_smul, mul_smul,
    h4 k AA M r s a b a' b' κ σ₀ H i R]

theorem tH_zero_X (h1 : OrdLin) (h2 : OrdX) (H : Hyp a b a' b' κ σ₀) (i : Fin r)
    (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    tH h1 a a' κ σ₀ 0 (X (Sum.inl i) * R) = a i • tH h1 a a' κ σ₀ 0 R := by
  simp only [tH_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
    Module.End.one_apply]
  rw [h2 k AA r s a a' (fun i i' => (H.h1 i i').1) i R, mul_smul]

theorem tH_succ_X (h1 : OrdLin) (h2 : OrdX) (g1 : Gen.PowXL) (g2 : Gen.CommL) (H : Hyp a b a' b' κ σ₀)
    (i : Fin r) (n : ℕ) (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    tH h1 a a' κ σ₀ (n + 1) (X (Sum.inl i) * R) =
      a i • tH h1 a a' κ σ₀ (n + 1) R + tH h1 a a' κ σ₀ n (Gen.dL κ i R) := by
  simp only [tH_apply]
  have hd : delta κ = Gen.gdelta κ := rfl
  rw [hd, g1 k (Fin r) (Fin s) κ i R n, g2 k (Fin r) (Fin s) κ i R n, smul_add, factorial_smul,
    ← mul_smul_comm, ordEval_add h1, h2 k AA r s a a' (fun i i' => (H.h1 i i').1) i, add_smul,
    mul_smul]

theorem psi_X (h1 : OrdLin) (h2 : OrdX) (g1 : Gen.PowXL) (g2 : Gen.CommL) (H : Hyp a b a' b' κ σ₀)
    (i : Fin r) (N : ℕ) (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    psi h1 a a' κ σ₀ (N + 1) (X (Sum.inl i) * R) =
      a i • psi h1 a a' κ σ₀ (N + 1) R + psi h1 a a' κ σ₀ N (Gen.dL κ i R) := by
  unfold psi
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun n => tH h1 a a' κ σ₀ n R)]
  simp only [tH_succ_X h1 h2 g1 g2 H, tH_zero_X h1 h2 H, Finset.sum_add_distrib, smul_add,
    Finset.smul_sum]
  abel

theorem psi_base (h1 : OrdLin) (g3 : Gen.VanL) (N : ℕ) (R : MvPolynomial (Fin r ⊕ Fin s) k)
    (hR : ∀ m ∈ R.support, xdeg m = 0) :
    psi h1 a a' κ σ₀ (N + 1) R = ordEval a a' R • σ₀ := by
  unfold psi
  rw [Finset.sum_range_succ']
  have hz : ∀ n, tH h1 a a' κ σ₀ (n + 1) R = 0 := by
    intro n
    have hd : delta κ = Gen.gdelta κ := rfl
    rw [tH_apply, hd, g3 k (Fin r) (Fin s) κ R (n + 1) (fun m hm => by
      have := hR m hm
      unfold xdeg at this
      omega), smul_zero, ordEval_zero h1, zero_smul]
  simp only [hz, Finset.sum_const_zero, zero_add, tH_apply, Nat.factorial_zero, Nat.cast_one,
    inv_one, one_smul, pow_zero, Module.End.one_apply]

theorem claim (h1 : OrdLin) (h2 : OrdX) (h3 : Base) (h4 : BComm) (g1 : Gen.PowXL) (g2 : Gen.CommL)
    (g3 : Gen.VanL) (H : Hyp a b a' b' κ σ₀) (d : ℕ) :
    ∀ R : MvPolynomial (Fin r ⊕ Fin s) k, (∀ m ∈ R.support, xdeg m ≤ d) → ∀ N, d < N →
      phiH h1 a b a' b' σ₀ R = psi h1 a a' κ σ₀ N R := by
  induction d with
  | zero =>
    intro R hR N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [psi_base h1 g3 N' R (fun m hm => Nat.le_zero.mp (hR m hm)), phiH_apply]
    apply h3 k AA M r s a b a' b' κ σ₀ H R
    intro m hm i
    have := hR m hm
    unfold xdeg at this
    exact Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp this) i (Finset.mem_univ _)
  | succ d ih =>
    intro R hR N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [R.as_sum, map_sum, psi_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmd := hR m hm
    by_cases h0 : xdeg m = 0
    · refine ih _ (fun u hu => ?_) _ (by omega)
      have hu' := MvPolynomial.support_monomial_subset hu
      rw [Finset.mem_singleton] at hu'
      subst hu'
      omega
    · have h0' : ∑ i, m (Sum.inl i) ≠ 0 := h0
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0'
      obtain ⟨m', hm'd⟩ : ∃ m', m' = m - Finsupp.single (Sum.inl i) 1 := ⟨_, rfl⟩
      have hm' : m = Finsupp.single (Sum.inl i) 1 + m' := by
        ext x
        by_cases hx : x = Sum.inl i
        · subst hx
          simp [hm'd]
          omega
        · simp [hm'd, Finsupp.single_apply, Ne.symm hx]
      have hxm' : xdeg m' ≤ d := by
        have := xdeg_add (Finsupp.single (Sum.inl i : Fin r ⊕ Fin s) 1) m'
        rw [← hm', xdeg_single] at this
        omega
      have hmon : monomial m (coeff m R) = X (Sum.inl i) * monomial m' (coeff m R) := by
        rw [X, monomial_mul, one_mul, ← hm']
      rw [hmon, phi_X h1 h2 h4 H, psi_X h1 h2 g1 g2 H]
      have e1 := ih (monomial m' (coeff m R)) (fun u hu => by
        have hu' := MvPolynomial.support_monomial_subset hu
        rw [Finset.mem_singleton] at hu'
        rw [hu']
        exact hxm') (N' + 1) (by omega)
      have e2 := ih (Gen.dL κ i (monomial m' (coeff m R)))
        (fun u hu => (dL_monomial_support κ i m' _ u hu).trans hxm') N' (by omega)
      rw [e1, e2]

end

end PI.WickFormula.Asm

namespace PI.WickFormula

open Asm in
theorem wickFormula_of (h1 : OrdLin) (h2 : OrdX) (h3 : Base) (h4 : BComm) (g1 : Gen.PowXL)
    (g2 : Gen.CommL) (g3 : Gen.VanL) : PI.WickFormula := by
  intro k AA M _ _ _ _ _ _ r s a b a' b' κ σ₀ e1 e2 e3 e4 e5 e6 P
  have H : Hyp a b a' b' κ σ₀ := ⟨e1, e2, e3, e4, e5, e6⟩
  have h := claim h1 h2 h3 h4 g1 g2 g3 H P.totalDegree P
    (fun m hm => xdeg_le_totalDegree P m hm) (P.totalDegree + 1) (by omega)
  rw [phiH_apply] at h
  rw [h]
  rfl

end PI.WickFormula
