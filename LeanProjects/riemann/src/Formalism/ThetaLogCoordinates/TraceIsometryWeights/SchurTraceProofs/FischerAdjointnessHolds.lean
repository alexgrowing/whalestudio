import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementD

namespace Formalism.InvariantFactorPaths.PW

open MvPolynomial Finset Formalism.GM.M

section fockForm

variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem fock_eq_sum' (F G : MvPolynomial σ ℚ_[p]) (s : Finset (σ →₀ ℕ)) (hs : F.support ⊆ s) :
    fock p F G = ∑ m ∈ s, F.coeff m * G.coeff m * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by
  unfold fock
  refine Finset.sum_subset hs fun m _ hm => ?_
  have h0 : F.coeff m = 0 := by simpa using hm
  rw [h0, zero_mul, zero_mul]

theorem fock_symm' (F G : MvPolynomial σ ℚ_[p]) : fock p F G = fock p G F := by
  classical
  rw [fock_eq_sum' F G (F.support ∪ G.support) Finset.subset_union_left,
    fock_eq_sum' G F (F.support ∪ G.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem fock_add_right' (F G G' : MvPolynomial σ ℚ_[p]) : fock p F (G + G') = fock p F G + fock p F G' := by
  unfold fock
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]
  ring

theorem fock_smul_right' (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) : fock p F (c • G) = c * fock p F G := by
  unfold fock
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

theorem fock_add_left' (F F' G : MvPolynomial σ ℚ_[p]) : fock p (F + F') G = fock p F G + fock p F' G := by
  rw [fock_symm', fock_add_right', fock_symm' F, fock_symm' F']

theorem fock_smul_left' (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) : fock p (c • F) G = c * fock p F G := by
  rw [fock_symm', fock_smul_right', fock_symm']

theorem fock_zero_left' (G : MvPolynomial σ ℚ_[p]) : fock p 0 G = 0 := by
  simp [fock]

theorem fock_zero_right' (F : MvPolynomial σ ℚ_[p]) : fock p F 0 = 0 := by
  simp [fock]

theorem fock_neg_right' (F G : MvPolynomial σ ℚ_[p]) : fock p F (-G) = -fock p F G := by
  rw [← neg_one_smul ℚ_[p] G, fock_smul_right', neg_one_mul]

theorem fock_neg_left' (F G : MvPolynomial σ ℚ_[p]) : fock p (-F) G = -fock p F G := by
  rw [fock_symm', fock_neg_right', fock_symm']

theorem fock_sum_left' {ι : Type} (t : Finset ι) (F : ι → MvPolynomial σ ℚ_[p]) (G : MvPolynomial σ ℚ_[p]) :
    fock p (∑ i ∈ t, F i) G = ∑ i ∈ t, fock p (F i) G := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [fock_zero_left']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add_left', ih]

theorem fock_sum_right' {ι : Type} (t : Finset ι) (F : MvPolynomial σ ℚ_[p]) (G : ι → MvPolynomial σ ℚ_[p]) :
    fock p F (∑ i ∈ t, G i) = ∑ i ∈ t, fock p F (G i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [fock_zero_right']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add_right', ih]

theorem facProd_ne_zero (m : σ →₀ ℕ) : (m.prod fun _ k => (k.factorial : ℚ_[p])) ≠ 0 := by
  rw [Finsupp.prod]
  exact Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast Nat.factorial_ne_zero _

theorem facProd_add_single (m : σ →₀ ℕ) (i : σ) :
    ((m + Finsupp.single i 1).prod fun _ k => (k.factorial : ℚ_[p])) =
      ((m i : ℚ_[p]) + 1) * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by
  classical
  have hs1 : (m + Finsupp.single i 1).support ⊆ insert i m.support := by
    intro x hx
    by_cases h : x = i
    · rw [h]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finsupp.mem_support_iff] at hx ⊢
      have h1 : (Finsupp.single i 1 : σ →₀ ℕ) x = 0 := by simp [Finsupp.single_apply, Ne.symm h]
      simpa [h1] using hx
  have hs2 : m.support ⊆ insert i m.support := Finset.subset_insert _ _
  rw [Finsupp.prod_of_support_subset _ hs1 _ (by simp),
    Finsupp.prod_of_support_subset _ hs2 _ (by simp),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i m.support),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i m.support), ← mul_assoc]
  congr 1
  · simp [Nat.factorial_succ]
  · refine Finset.prod_congr rfl fun x hx => ?_
    have hx' : x ≠ i := Finset.ne_of_mem_erase hx
    have h1 : (Finsupp.single i 1 : σ →₀ ℕ) x = 0 := by simp [Finsupp.single_apply, Ne.symm hx']
    rw [Finsupp.add_apply, h1, add_zero]

theorem fock_X_mul' (i : σ) (g h : MvPolynomial σ ℚ_[p]) :
    fock p (X i * g) h = fock p g (pderiv i h) := by
  classical
  unfold fock
  rw [support_X_mul, Finset.sum_map]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [addLeftEmbedding_apply]
  rw [coeff_X_mul, coeff_pderiv, add_comm (Finsupp.single i 1) m, facProd_add_single]
  ring

theorem fock_monomial_right (F : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) (a : ℚ_[p]) :
    fock p F (monomial m a) = F.coeff m * a * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by
  classical
  rw [fock_symm', fock_eq_sum' _ _ {m} support_monomial_subset, Finset.sum_singleton,
    coeff_monomial, if_pos rfl]
  ring

theorem fock_nondeg (F : MvPolynomial σ ℚ_[p]) (h : ∀ G, fock p F G = 0) : F = 0 := by
  ext m
  have h1 := h (monomial m 1)
  rw [fock_monomial_right, mul_one] at h1
  rw [coeff_zero]
  exact (mul_eq_zero.1 h1).resolve_right (facProd_ne_zero m)

theorem fock_disjoint (F G : MvPolynomial σ ℚ_[p]) (h : ∀ m ∈ F.support, m ∉ G.support) : fock p F G = 0 := by
  unfold fock
  refine Finset.sum_eq_zero fun m hm => ?_
  have h0 : G.coeff m = 0 := by simpa using h m hm
  rw [h0, mul_zero, zero_mul]

theorem intPol_iff_norm (x : MvPolynomial σ ℚ_[p]) : x ∈ IntPol p σ ↔ ∀ m, ‖x.coeff m‖ ≤ 1 := by
  constructor
  · rintro ⟨y, rfl⟩ m
    simp only [AlgHom.toLinearMap_apply, mapAlgHom_apply, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    refine ⟨∑ m ∈ x.support, monomial m (⟨x.coeff m, h m⟩ : ℤ_[p]), ?_⟩
    simp only [AlgHom.toLinearMap_apply, map_sum, mapAlgHom_apply, map_monomial]
    conv_rhs => rw [x.as_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    erw [map_monomial]
    rfl

end fockForm

theorem fischerAdjointness_holds : FockAdj := by
  intro p _ N r LL j c d F G
  have key : ∀ (a b : Fin N × Fin r) (F G : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      fock p (X a * pderiv b F) G = fock p F (X b * pderiv a G) := by
    intro a b F G
    rw [fock_X_mul', fock_symm' F, fock_X_mul', fock_symm']
  unfold glAct
  rw [LinearMap.sum_apply, LinearMap.sum_apply, fock_sum_left', fock_sum_right']
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h1 h2
  · simpa using key (i, c) (i, d) F G
  · simp [fock_neg_left', fock_neg_right', key]
  · simp [fock_zero_left', fock_zero_right']

section divided

variable {K A : Type} [Field K] [CharZero K] [CommRing A] [Algebra K A]

theorem divPow_mul (D : A →ₗ[K] A) (hD : ∀ a b, D (a * b) = a * D b + b * D a) (k : ℕ) (f g : A) :
    ((k.factorial : K))⁻¹ • (D ^ k) (f * g) =
      ∑ ij ∈ antidiagonal k, (((ij.1.factorial : K))⁻¹ • (D ^ ij.1) f) * (((ij.2.factorial : K))⁻¹ • (D ^ ij.2) g) := by
  let dd : ℕ → A → A := fun k f => ((k.factorial : K))⁻¹ • (D ^ k) f
  have hdd : ∀ k f, dd k f = ((k.factorial : K))⁻¹ • (D ^ k) f := fun _ _ => rfl
  have hD1 : ∀ k f, D (dd k f) = ((k + 1 : ℕ) : K) • dd (k + 1) f := by
    intro k f
    rw [hdd, hdd, map_smul, pow_succ', Module.End.mul_apply, smul_smul]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul]
    have h1 : ((k.factorial : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have h2 : ((k + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    field_simp
  show dd k (f * g) = ∑ ij ∈ antidiagonal k, dd ij.1 f * dd ij.2 g
  induction k with
  | zero => simp [hdd]
  | succ k ih =>
    have hk : ((k + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hL : dd (k + 1) (f * g) = ((k + 1 : ℕ) : K)⁻¹ • D (dd k (f * g)) := by
      rw [hD1, smul_smul, inv_mul_cancel₀ hk, one_smul]
    rw [hL, ih, map_sum]
    simp only [hD, hD1, mul_smul_comm, Finset.sum_add_distrib]
    rw [inv_smul_eq_iff₀ hk]
    have hsplit : ((k + 1 : ℕ) : K) • ∑ ij ∈ antidiagonal (k + 1), dd ij.1 f * dd ij.2 g
        = ∑ ij ∈ antidiagonal (k + 1), ((ij.2 : ℕ) : K) • (dd ij.1 f * dd ij.2 g)
          + ∑ ij ∈ antidiagonal (k + 1), ((ij.1 : ℕ) : K) • (dd ij.1 f * dd ij.2 g) := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ij hij => ?_
      have hij' : ij.1 + ij.2 = k + 1 := by simpa using hij
      rw [← add_smul, ← Nat.cast_add, add_comm ij.2, hij']
    rw [hsplit, Finset.Nat.sum_antidiagonal_succ', Finset.Nat.sum_antidiagonal_succ]
    simp only [Nat.cast_zero, zero_smul, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [mul_comm]

end divided

section glDivided

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

private theorem glAct_eq_sum_X_mul_pderiv (LL : Letters N) (j : ℕ) (c d : Fin r)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j c d F = ∑ i : Fin N, if (i : ℕ) < j then
      (if LL.vec i = true then X (i, c) * pderiv (i, d) F else -(X (i, d) * pderiv (i, c) F))
      else 0 := by
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

private theorem glAct_X_apply (LL : Letters N) (j : ℕ) (c d : Fin r) (i : Fin N) (e : Fin r) :
    glAct p LL j c d (X (i, e)) = if (i : ℕ) < j then
      (if LL.vec i = true then (if e = d then X (i, c) else 0)
        else (if e = c then -X (i, d) else 0)) else 0 := by
  classical
  rw [glAct_eq_sum_X_mul_pderiv, Finset.sum_eq_single i]
  · split_ifs <;> simp_all [pderiv_X, Pi.single_apply]
  · intro k _ hk
    split_ifs <;> simp [pderiv_X, Pi.single_apply, hk, Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem glAct_C' (LL : Letters N) (j : ℕ) (c d : Fin r) (a : ℚ_[p]) : glAct p LL j c d (C a) = 0 := by
  rw [glAct_eq_sum_X_mul_pderiv]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs <;> simp

theorem glAct_glAct_X (LL : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d) (v : Fin N × Fin r) :
    glAct p LL j c d (glAct p LL j c d (X v)) = 0 := by
  obtain ⟨i, e⟩ := v
  rw [glAct_X_apply]
  split_ifs <;> simp_all [glAct_X_apply, hcd, Ne.symm hcd]

private theorem X_mem_intPol (w : Fin N × Fin r) :
    (X w : MvPolynomial (Fin N × Fin r) ℚ_[p]) ∈ IntPol p (Fin N × Fin r) :=
  LinearMap.mem_range.2 ⟨X w, by simp⟩

theorem glAct_X_int (LL : Letters N) (j : ℕ) (c d : Fin r) (v : Fin N × Fin r) :
    glAct p LL j c d (X v) ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨i, e⟩ := v
  rw [glAct_X_apply]
  split_ifs <;> first
    | exact X_mem_intPol _
    | exact Submodule.zero_mem _
    | exact Submodule.neg_mem _ (X_mem_intPol _)

theorem divPow_X_int (LL : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d) (v : Fin N × Fin r) (k : ℕ) :
    ((k.factorial : ℚ_[p]))⁻¹ • ((glAct p LL j c d) ^ k) (X v) ∈ IntPol p (Fin N × Fin r) := by
  rcases k with _ | _ | k
  · simpa using X_mem_intPol v
  · simpa using glAct_X_int LL j c d v
  · rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply,
      glAct_glAct_X LL j c d hcd v, map_zero, smul_zero]
    exact Submodule.zero_mem _

theorem divPow_C_int (LL : Letters N) (j : ℕ) (c d : Fin r) (a : ℤ_[p]) (k : ℕ) :
    ((k.factorial : ℚ_[p]))⁻¹ • ((glAct p LL j c d) ^ k) (C (algebraMap ℤ_[p] ℚ_[p] a)) ∈ IntPol p (Fin N × Fin r) := by
  rcases k with _ | k
  · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero, Module.End.one_apply]
    exact LinearMap.mem_range.2 ⟨C a, by simp⟩
  · rw [pow_succ, Module.End.mul_apply, glAct_C', map_zero, smul_zero]
    exact Submodule.zero_mem _

end glDivided

private theorem glAct_mul_eq_mul_glAct_add_mul_glAct {p : ℕ} [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (c d : Fin r)
    (a b : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j c d (a * b) = a * glAct p LL j c d b + b * glAct p LL j c d a := by
  rw [glAct_eq_sum_X_mul_pderiv, glAct_eq_sum_X_mul_pderiv, glAct_eq_sum_X_mul_pderiv, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Derivation.leibniz] <;> ring

theorem divided_integral_holds : DivInt := by
  intro p _ N r LL j c d hcd k x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
  let Pr : MvPolynomial (Fin N × Fin r) ℚ_[p] → Prop := fun z => ∀ k : ℕ,
    ((k.factorial : ℚ_[p]))⁻¹ • ((glAct p LL j c d) ^ k) z ∈ IntPol p (Fin N × Fin r)
  have hmul : ∀ u w, Pr u → Pr w → Pr (u * w) := by
    intro u w hu hw k
    rw [divPow_mul (glAct p LL j c d) (glAct_mul_eq_mul_glAct_add_mul_glAct LL j c d) k u w]
    refine Submodule.sum_mem _ fun ij _ => ?_
    obtain ⟨u', hu'⟩ := LinearMap.mem_range.1 (hu ij.1)
    obtain ⟨w', hw'⟩ := LinearMap.mem_range.1 (hw ij.2)
    exact LinearMap.mem_range.2 ⟨u' * w', by rw [← hu', ← hw']; simp⟩
  have hadd : ∀ u w, Pr u → Pr w → Pr (u + w) := by
    intro u w hu hw k
    rw [map_add, smul_add]
    exact Submodule.add_mem _ (hu k) (hw k)
  have hall : ∀ y : MvPolynomial (Fin N × Fin r) ℤ_[p],
      Pr (MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) y) := by
    intro y
    induction y using MvPolynomial.induction_on
    next a =>
      rw [map_C]
      exact fun k => divPow_C_int LL j c d a k
    next u w hu hw =>
      rw [map_add]
      exact hadd _ _ hu hw
    next u v hu =>
      rw [map_mul, map_X]
      exact hmul _ _ hu (fun k => divPow_X_int LL j c d hcd v k)
  exact hall y k

end Formalism.InvariantFactorPaths.PW
