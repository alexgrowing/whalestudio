import Formalism.PolynomialDimension.StatementHar

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.CountingSumsFrames

section DivPow

variable {K E : Type*} [Field K] [CharZero K] [Ring E] [Algebra K E]

theorem divPow_add_mem (S : Subsemiring E) (a b : E) (hab : Commute a b)
    (ha : ∀ n : ℕ, ((n.factorial : K)⁻¹) • a ^ n ∈ S) (hb : ∀ n : ℕ, ((n.factorial : K)⁻¹) • b ^ n ∈ S)
    (n : ℕ) : ((n.factorial : K)⁻¹) • (a + b) ^ n ∈ S := by
  rw [hab.add_pow', Finset.smul_sum]
  refine S.sum_mem ?_
  rintro ⟨i, j⟩ hij
  have hn : i + j = n := by simpa using hij
  subst hn
  have key : (((i + j).factorial : K)⁻¹) • ((i + j).choose i • (a ^ i * b ^ j)) =
      (((i.factorial : K)⁻¹) • a ^ i) * (((j.factorial : K)⁻¹) • b ^ j) := by
    rw [smul_mul_smul_comm, ← Nat.cast_smul_eq_nsmul K, smul_smul]
    congr 1
    have h1 : (((i + j).choose i * i.factorial * j.factorial : ℕ) : K) = ((i + j).factorial : K) := by
      rw [Nat.choose_symm_add, Nat.add_choose_mul_factorial_mul_factorial]
    have hi : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
    have hj : (j.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
    have hij' : ((i + j).factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    push_cast at h1
    field_simp
    linear_combination h1
  simp only
  rw [key]
  exact S.mul_mem (ha i) (hb j)

theorem divPow_sum_mem {ι : Type*} (S : Subsemiring E) (s : Finset ι) (a : ι → E)
    (hc : ∀ i j, Commute (a i) (a j)) (ha : ∀ (i : ι) (n : ℕ), ((n.factorial : K)⁻¹) • a i ^ n ∈ S) :
    ∀ n : ℕ, ((n.factorial : K)⁻¹) • (∑ i ∈ s, a i) ^ n ∈ S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [zero_pow hn.ne']
  | insert i s hi ih =>
    intro n
    rw [Finset.sum_insert hi]
    exact divPow_add_mem S _ _ (Commute.sum_right _ _ _ fun j _ => hc i j) (ha i) ih n

def stabilizerSubsemiring {V : Type*} [AddCommGroup V] [Module K V] (L : Set V)
    (hadd : ∀ f g, f ∈ L → g ∈ L → f + g ∈ L) (h0 : (0 : V) ∈ L) : Subsemiring (Module.End K V) where
  carrier := {T | ∀ f ∈ L, T f ∈ L}
  mul_mem' := by
    intro S T hS hT f hf
    exact hS _ (hT _ hf)
  one_mem' := by
    intro f hf
    exact hf
  add_mem' := by
    intro S T hS hT f hf
    exact hadd _ _ (hS _ hf) (hT _ hf)
  zero_mem' := by
    intro f _
    exact h0

end DivPow

theorem pow_log_div_choose_mem {K : Type} [Field K] [CharZero K] (R : Subring K) (p : ℕ) (hp : p.Prime) (hR : PLocal R p)
    (n N l : ℕ) (hn : n ≤ N) : (p : K) ^ Nat.log p N / ((n.choose l : ℕ) : K) ∈ R := by
  by_cases hc : n.choose l = 0
  · rw [hc]; simp
  · obtain ⟨e, u, hu, hcu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc p hp.ne_one
    have he : e ≤ Nat.log p N := by
      have h1 : p ^ e ∣ n.choose l := ⟨u, hcu⟩
      have h2 : e ≤ (n.choose l).factorization p := (hp.pow_dvd_iff_le_factorization hc).1 h1
      exact h2.trans (Nat.factorization_choose_le_log.trans (Nat.log_mono_right hn))
    have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hu0 : (u : K) ≠ 0 := by
      refine Nat.cast_ne_zero.2 ?_
      rintro rfl
      exact hu (dvd_zero p)
    have : (p : K) ^ Nat.log p N / ((n.choose l : ℕ) : K) = (p : K) ^ (Nat.log p N - e) * (u : K)⁻¹ := by
      rw [hcu]
      push_cast
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le he
      rw [hd, Nat.add_sub_cancel_left, pow_add]
      field_simp
    rw [this]
    exact R.mul_mem (R.pow_mem (natCast_mem R p) _) (hR u hu)

section Coeff

variable {K : Type} [Field K] [CharZero K] {k : ℕ}

def h3s (i : Fin k) (n : ℕ) : XY k →₀ ℕ := Finsupp.single (Sum.inl i) n + Finsupp.single (Sum.inr i) n

theorem diagExponent_inl (i j : Fin k) (n : ℕ) : h3s i n (Sum.inl j) = if i = j then n else 0 := by
  simp [h3s, Finsupp.single_apply]

theorem diagExponent_inr (i j : Fin k) (n : ℕ) : h3s i n (Sum.inr j) = if i = j then n else 0 := by
  simp [h3s, Finsupp.single_apply]

theorem factorial_add_eq_descFactorial_mul (a n : ℕ) : (a + n).factorial = (a + n).descFactorial n * a.factorial := by
  have := Nat.factorial_mul_descFactorial (Nat.le_add_left n a)
  rw [Nat.add_sub_cancel] at this
  rw [← this, mul_comm]

theorem xFactorial_add_diagExponent (m : XY k →₀ ℕ) (i : Fin k) (n : ℕ) :
    xFact (m + h3s i n) = (m (Sum.inl i) + n).descFactorial n * xFact m := by
  classical
  unfold xFact
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i), ← Finset.mul_prod_erase univ (fun j => (m (Sum.inl j)).factorial) (Finset.mem_univ i)]
  have h1 : ∏ j ∈ univ.erase i, ((m + h3s i n) (Sum.inl j)).factorial =
      ∏ j ∈ univ.erase i, (m (Sum.inl j)).factorial := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    simp [diagExponent_inl, this]
  rw [h1]
  simp only [Finsupp.add_apply, diagExponent_inl, if_true]
  rw [factorial_add_eq_descFactorial_mul, mul_assoc]

def h3e (K : Type) [Field K] {k : ℕ} (i : Fin k) : Module.End K (PolXY K k) :=
  LinearMap.mulLeft K (X (Sum.inl i) * X (Sum.inr i))

def h3d (K : Type) [Field K] {k : ℕ} (i : Fin k) : Module.End K (PolXY K k) :=
  (pderiv (R := K) (Sum.inl i : XY k)).toLinearMap ∘ₗ (pderiv (R := K) (Sum.inr i : XY k)).toLinearMap

theorem diagLaplacian_apply (i : Fin k) (f : PolXY K k) :
    h3d K i f = pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := rfl

theorem diagMul_pow_apply (i : Fin k) (n : ℕ) (f : PolXY K k) :
    (h3e K i ^ n) f = monomial (h3s i n) (1 : K) * f := by
  have : (monomial (h3s i n) (1 : K) : PolXY K k) = (X (Sum.inl i) * X (Sum.inr i)) ^ n := by
    rw [mul_pow, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul, h3s]
  rw [this, h3e, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]

theorem coeff_diagMul_pow (i : Fin k) (n : ℕ) (f : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m ((h3e K i ^ n) f) = if h3s i n ≤ m then coeff (m - h3s i n) f else 0 := by
  rw [diagMul_pow_apply, coeff_monomial_mul', one_mul]

theorem coeff_diagLaplacian_pow (i : Fin k) (n : ℕ) : ∀ (f : PolXY K k) (m : XY k →₀ ℕ),
    coeff m ((h3d K i ^ n) f) = coeff (m + h3s i n) f *
      (((m (Sum.inl i) + n).descFactorial n : ℕ) * ((m (Sum.inr i) + n).descFactorial n : ℕ)) := by
  induction n with
  | zero => intro f m; simp [h3s]
  | succ n ih =>
    intro f m
    rw [pow_succ, Module.End.mul_apply, ih]
    have h1 : coeff (m + h3s i n) (h3d K i f) = coeff (m + h3s i (n + 1)) f *
        (((m (Sum.inl i) + n + 1 : ℕ) : K) * ((m (Sum.inr i) + n + 1 : ℕ) : K)) := by
      simp only [diagLaplacian_apply, coeff_pderiv]
      have e : m + h3s i n + Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1 = m + h3s i (n + 1) := by
        simp only [h3s, Finsupp.single_add]
        abel
      rw [e]
      simp [diagExponent_inl, diagExponent_inr]
      ring
    rw [h1, ← add_assoc, ← add_assoc, Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ]
    push_cast
    ring

theorem diagMul_commute (i j : Fin k) : Commute (h3e K i) (h3e K j) := by
  refine LinearMap.ext fun f => ?_
  simp only [Module.End.mul_apply, h3e, LinearMap.mulLeft_apply]
  ring

theorem diagLaplacian_commute (i j : Fin k) : Commute (h3d K i) (h3d K j) := by
  refine LinearMap.ext fun f => ?_
  ext m
  simp only [Module.End.mul_apply, diagLaplacian_apply, coeff_pderiv]
  have e : m + Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1 + Finsupp.single (Sum.inl j) 1 +
      Finsupp.single (Sum.inr j) 1 = m + Finsupp.single (Sum.inl j) 1 + Finsupp.single (Sum.inr j) 1 +
      Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1 := by abel
  rw [e]
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : ¬ j = i := fun h => hij h.symm
    simp [hij, hji]
    ring

theorem pairingDivPow_eq (l : ℕ) : hDiv K k l = ((l.factorial : K)⁻¹) • (∑ i : Fin k, h3e K i) ^ l := by
  have : (∑ i : Fin k, h3e K i) = LinearMap.mulLeft K (hXY K k) := by
    refine LinearMap.ext fun f => ?_
    simp [h3e, hXY, Finset.sum_mul, LinearMap.sum_apply, mul_assoc]
  rw [this, LinearMap.pow_mulLeft, hDiv]

theorem laplacianDivPow_eq (l : ℕ) : ctrDiv K k l = ((l.factorial : K)⁻¹) • (∑ i : Fin k, h3d K i) ^ l := rfl

end Coeff

section Std

variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem descFactorial_cast_eq (a n : ℕ) :
    (((a + n).descFactorial n : ℕ) : K) = (n.factorial : K) * (((a + n).choose n : ℕ) : K) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring

theorem zero_mem_fockLattice (R : Subring K) : (0 : PolXY K k) ∈ FockLat R := by
  intro m; simp

theorem add_mem_fockLattice (R : Subring K) (f g : PolXY K k) (hf : f ∈ FockLat R) (hg : g ∈ FockLat R) :
    f + g ∈ FockLat R := by
  intro m
  rw [coeff_add, mul_add]
  exact R.add_mem (hf m) (hg m)

theorem smul_mem_fockLattice (R : Subring K) (r : K) (hr : r ∈ R) (f : PolXY K k) (hf : f ∈ FockLat R) :
    r • f ∈ FockLat R := by
  intro m
  rw [coeff_smul, smul_eq_mul, mul_left_comm]
  exact R.mul_mem hr (hf m)

theorem diagMul_divPow_mem_fockLattice (R : Subring K) (i : Fin k) (n : ℕ) (f : PolXY K k) (hf : f ∈ FockLat R) :
    (((n.factorial : K)⁻¹) • h3e K i ^ n) f ∈ FockLat R := by
  intro m
  rw [LinearMap.smul_apply, coeff_smul, smul_eq_mul, coeff_diagMul_pow]
  split_ifs with h
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + h3s i n := ⟨m - h3s i n, (tsub_add_cancel_of_le h).symm⟩
    rw [add_tsub_cancel_right, xFactorial_add_diagExponent]
    have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    have : (((m' (Sum.inl i) + n).descFactorial n * xFact m' : ℕ) : K) * ((n.factorial : K)⁻¹ * coeff m' f) =
        (((m' (Sum.inl i) + n).choose n : ℕ) : K) * ((xFact m' : K) * coeff m' f) := by
      rw [Nat.cast_mul, descFactorial_cast_eq]
      field_simp
    rw [this]
    exact R.mul_mem (natCast_mem R _) (hf m')
  · simp

theorem diagLaplacian_divPow_mem_fockLattice (R : Subring K) (i : Fin k) (n : ℕ) (f : PolXY K k) (hf : f ∈ FockLat R) :
    (((n.factorial : K)⁻¹) • h3d K i ^ n) f ∈ FockLat R := by
  intro m
  rw [LinearMap.smul_apply, coeff_smul, smul_eq_mul, coeff_diagLaplacian_pow]
  have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have h1 := hf (m + h3s i n)
  rw [xFactorial_add_diagExponent] at h1
  have : (xFact m : K) * ((n.factorial : K)⁻¹ * (coeff (m + h3s i n) f *
        ((((m (Sum.inl i) + n).descFactorial n : ℕ) : K) * (((m (Sum.inr i) + n).descFactorial n : ℕ) : K)))) =
      (((m (Sum.inr i) + n).choose n : ℕ) : K) *
        ((((m (Sum.inl i) + n).descFactorial n * xFact m : ℕ) : K) * coeff (m + h3s i n) f) := by
    rw [Nat.cast_mul, descFactorial_cast_eq (m (Sum.inr i))]
    field_simp
  rw [this]
  exact R.mul_mem (natCast_mem R _) h1

theorem divPow_mem_of_generators (L : Set (PolXY K k)) (hadd : ∀ f g, f ∈ L → g ∈ L → f + g ∈ L) (h0 : (0 : PolXY K k) ∈ L)
    (he : ∀ (i : Fin k) (n : ℕ) (f : PolXY K k), f ∈ L → (((n.factorial : K)⁻¹) • h3e K i ^ n) f ∈ L)
    (hd : ∀ (i : Fin k) (n : ℕ) (f : PolXY K k), f ∈ L → (((n.factorial : K)⁻¹) • h3d K i ^ n) f ∈ L)
    (l : ℕ) (f : PolXY K k) (hf : f ∈ L) : hDiv K k l f ∈ L ∧ ctrDiv K k l f ∈ L := by
  constructor
  · rw [pairingDivPow_eq]
    exact divPow_sum_mem (K := K) (stabilizerSubsemiring (K := K) L hadd h0) univ (fun i => h3e K i) diagMul_commute
      (fun i n => he i n) l f hf
  · rw [laplacianDivPow_eq]
    exact divPow_sum_mem (K := K) (stabilizerSubsemiring (K := K) L hadd h0) univ (fun i => h3d K i) diagLaplacian_commute
      (fun i n => hd i n) l f hf

end Std

section SubstGL

variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem linearSubst_pairing (g : GL (Fin k) K) : glAct g (hXY K k) = hXY K k := by
  have hg : ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) * (g : Matrix (Fin k) (Fin k) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul]; simp
  simp only [glAct, hXY, map_sum, map_mul, aeval_X, Sum.elim_inl, Sum.elim_inr]
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  have : ∀ l : Fin k, ∑ i : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j) *
      (C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) * X (Sum.inr l)) =
      C ((1 : Matrix (Fin k) (Fin k) K) l j) * ((X (Sum.inl j) : PolXY K k) * X (Sum.inr l)) := by
    intro l
    rw [← hg, Matrix.mul_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [C_mul]; ring
  simp only [this, Matrix.one_apply]
  simp [Finset.sum_ite_eq']

theorem pderiv_aeval_eq_sum_chain_rule {σ : Type} [Fintype σ] (u : σ → MvPolynomial σ K) (v : σ) (f : MvPolynomial σ K) :
    pderiv v (aeval u f) = ∑ w : σ, aeval u (pderiv w f) * pderiv v (u w) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, map_add, pderiv_X, add_mul,
      Finset.sum_add_distrib]
    have h1 : ∑ w : σ, aeval u p * aeval u ((Pi.single w 1 : σ → MvPolynomial σ K) n) * pderiv v (u w) =
        aeval u p * pderiv v (u n) := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · intro h; exact absurd (Finset.mem_univ n) h
    rw [h1, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

theorem pderiv_inl_linearSubst (g : GL (Fin k) K) (j : Fin k) (f : PolXY K k) :
    pderiv (Sum.inl j) (glAct g f) =
      ∑ i : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * glAct g (pderiv (Sum.inl i) f) := by
  classical
  unfold glAct
  rw [pderiv_aeval_eq_sum_chain_rule, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply]
  simp [mul_comm]

theorem pderiv_inr_linearSubst (g : GL (Fin k) K) (j : Fin k) (f : PolXY K k) :
    pderiv (Sum.inr j) (glAct g f) =
      ∑ i : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) * glAct g (pderiv (Sum.inr i) f) := by
  classical
  unfold glAct
  rw [pderiv_aeval_eq_sum_chain_rule, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply]
  simp [mul_comm]

theorem laplacian_apply' (f : PolXY K k) :
    ctrF K k f = ∑ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := by
  simp [ctrF, LinearMap.sum_apply]

theorem laplacian_linearSubst (g : GL (Fin k) K) (f : PolXY K k) : ctrF K k (glAct g f) = glAct g (ctrF K k f) := by
  have hg : (g : Matrix (Fin k) (Fin k) K) * ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul]; simp
  rw [laplacian_apply', laplacian_apply', map_sum]
  simp only [pderiv_inr_linearSubst, map_sum, pderiv_C_mul, pderiv_inl_linearSubst, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have : ∀ l : Fin k, ∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) *
        (C ((g : Matrix (Fin k) (Fin k) K) l j) * glAct g (pderiv (Sum.inl l) (pderiv (Sum.inr i) f))) =
      C ((1 : Matrix (Fin k) (Fin k) K) l i) * glAct g (pderiv (Sum.inl l) (pderiv (Sum.inr i) f)) := by
    intro l
    rw [← hg, Matrix.mul_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [C_mul]; ring
  simp only [this, Matrix.one_apply]
  simp [Finset.sum_ite_eq']

theorem pairingDivPow_linearSubst (g : GL (Fin k) K) (l : ℕ) (f : PolXY K k) :
    hDiv K k l (glAct g f) = glAct g (hDiv K k l f) := by
  simp only [hDiv, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_smul, map_mul, map_pow, linearSubst_pairing]

theorem laplacian_pow_linearSubst (g : GL (Fin k) K) (l : ℕ) : ∀ f : PolXY K k,
    (ctrF K k ^ l) (glAct g f) = glAct g ((ctrF K k ^ l) f) := by
  induction l with
  | zero => intro f; simp
  | succ l ih => intro f; rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, laplacian_linearSubst, ih]

theorem laplacianDivPow_linearSubst (g : GL (Fin k) K) (l : ℕ) (f : PolXY K k) :
    ctrDiv K k l (glAct g f) = glAct g (ctrDiv K k l f) := by
  simp only [ctrDiv, LinearMap.smul_apply, map_smul, laplacian_pow_linearSubst]

theorem divPow_mem_translateLattice (L : Set (PolXY K k))
    (hL : ∀ (l : ℕ) (f : PolXY K k), f ∈ L → hDiv K k l f ∈ L ∧ ctrDiv K k l f ∈ L)
    (g : GL (Fin k) K) (l : ℕ) (f : PolXY K k) (hf : f ∈ latOf g L) :
    hDiv K k l f ∈ latOf g L ∧ ctrDiv K k l f ∈ latOf g L := by
  obtain ⟨f0, hf0, rfl⟩ := hf
  exact ⟨⟨_, (hL l f0 hf0).1, (pairingDivPow_linearSubst g l f0).symm⟩, ⟨_, (hL l f0 hf0).2, (laplacianDivPow_linearSubst g l f0).symm⟩⟩

theorem zero_mem_translateLattice (L : Set (PolXY K k)) (h0 : (0 : PolXY K k) ∈ L) (g : GL (Fin k) K) :
    (0 : PolXY K k) ∈ latOf g L := ⟨0, h0, map_zero _⟩

theorem add_mem_translateLattice (L : Set (PolXY K k)) (hadd : ∀ f g, f ∈ L → g ∈ L → f + g ∈ L) (g : GL (Fin k) K)
    (f f' : PolXY K k) (hf : f ∈ latOf g L) (hf' : f' ∈ latOf g L) : f + f' ∈ latOf g L := by
  obtain ⟨a, ha, rfl⟩ := hf
  obtain ⟨b, hb, rfl⟩ := hf'
  exact ⟨a + b, hadd a b ha hb, map_add _ _ _⟩

theorem smul_mem_translateLattice (R : Subring K) (L : Set (PolXY K k)) (hs : ∀ r ∈ R, ∀ f ∈ L, r • f ∈ L) (g : GL (Fin k) K)
    (r : K) (hr : r ∈ R) (f : PolXY K k) (hf : f ∈ latOf g L) : r • f ∈ latOf g L := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact ⟨r • a, hs r hr a ha, map_smul _ _ _⟩

end SubstGL

section Proj

variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem pow_log_smul_harmonicProj_mem (R : Subring K) (p : ℕ) (hp : p.Prime) (hR : PLocal R p) (M : Set (PolXY K k))
    (h0 : (0 : PolXY K k) ∈ M) (hadd : ∀ f g, f ∈ M → g ∈ M → f + g ∈ M)
    (hs : ∀ r ∈ R, ∀ f ∈ M, r • f ∈ M)
    (hM : ∀ (l : ℕ) (f : PolXY K k), f ∈ M → hDiv K k l f ∈ M ∧ ctrDiv K k l f ∈ M)
    (a b N : ℕ) (hN : a + b + k ≤ N) (f : PolXY K k) (hf : f ∈ M) :
    ((p : K) ^ Nat.log p N) • harProj K k a b f ∈ M := by
  have hsum : ∀ (s : Finset ℕ) (F : ℕ → PolXY K k), (∀ l ∈ s, F l ∈ M) → ∑ l ∈ s, F l ∈ M := by
    classical
    intro s F
    induction s using Finset.induction_on with
    | empty => intro _; simpa using h0
    | insert i s hi ih =>
      intro h
      rw [Finset.sum_insert hi]
      exact hadd _ _ (h i (Finset.mem_insert_self i s)) (ih fun l hl => h l (Finset.mem_insert_of_mem hl))
  rw [harProj, LinearMap.sum_apply, Finset.smul_sum]
  refine hsum _ _ fun l _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply, smul_smul]
  refine hs _ ?_ _ (hM l _ (hM l f hf).2).1
  have : (p : K) ^ Nat.log p N * ((-1 : K) ^ l / (((a + b + k - 2).choose l : ℕ) : K)) =
      (-1 : K) ^ l * ((p : K) ^ Nat.log p N / (((a + b + k - 2).choose l : ℕ) : K)) := by ring
  rw [this]
  exact R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) l) (pow_log_div_choose_mem R p hp hR _ N l (by omega))

theorem pow_log_smul_isotypicProj_mem (R : Subring K) (p : ℕ) (hp : p.Prime) (hR : PLocal R p) (M : Set (PolXY K k))
    (h0 : (0 : PolXY K k) ∈ M) (hadd : ∀ f g, f ∈ M → g ∈ M → f + g ∈ M)
    (hs : ∀ r ∈ R, ∀ f ∈ M, r • f ∈ M)
    (hM : ∀ (l : ℕ) (f : PolXY K k), f ∈ M → hDiv K k l f ∈ M ∧ ctrDiv K k l f ∈ M)
    (A B j : ℕ) (hj : j ≤ A) (f : PolXY K k) (hf : f ∈ M) :
    ((p : K) ^ (2 * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ M := by
  have h1 : ((p : K) ^ Nat.log p (A + B + k)) • harProj K k (A - j) (B - j) (ctrDiv K k j f) ∈ M :=
    pow_log_smul_harmonicProj_mem R p hp hR M h0 hadd hs hM (A - j) (B - j) (A + B + k) (by omega) _ (hM j f hf).2
  have h2 := (hM j _ h1).1
  have h3 := hs _ (pow_log_div_choose_mem R p hp hR (A + B + k - 2 * j + j - 1) (A + B + k) j (by omega)) _ h2
  have : ((p : K) ^ (2 * Nat.log p (A + B + k))) • levelProj K k A B j f =
      ((p : K) ^ Nat.log p (A + B + k) / (((A + B + k - 2 * j + j - 1).choose j : ℕ) : K)) •
        hDiv K k j (((p : K) ^ Nat.log p (A + B + k)) • harProj K k (A - j) (B - j) (ctrDiv K k j f)) := by
    rw [levelProj, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_smul, smul_smul,
      smul_smul]
    congr 1
    rw [two_mul, pow_add]
    ring
  rw [this]
  exact h3

end Proj

theorem divPow_mem_fockLattice {K : Type} [Field K] [CharZero K] {k : ℕ} (R : Subring K) (l : ℕ) (f : PolXY K k)
    (hf : f ∈ FockLat R) : hDiv K k l f ∈ FockLat R ∧ ctrDiv K k l f ∈ FockLat R :=
  divPow_mem_of_generators (FockLat R) (add_mem_fockLattice R) (zero_mem_fockLattice R) (diagMul_divPow_mem_fockLattice R) (diagLaplacian_divPow_mem_fockLattice R) l f hf

theorem fockLatticeProjection_holds : FockProj := by
  intro K _ _ k A B p R g _ hp hR f _ hf
  have h0 := zero_mem_translateLattice (FockLat R) (zero_mem_fockLattice R) g
  have hadd := add_mem_translateLattice (FockLat R) (add_mem_fockLattice R) g
  have hs : ∀ r ∈ R, ∀ f ∈ latOf g (FockLat R), r • f ∈ latOf g (FockLat R) :=
    smul_mem_translateLattice R (FockLat R) (smul_mem_fockLattice R) g
  have hM := divPow_mem_translateLattice (FockLat R) (divPow_mem_fockLattice R) g
  exact ⟨pow_log_smul_harmonicProj_mem R p hp hR _ h0 hadd hs hM A B (A + B + k) le_rfl f hf,
    fun j hj => pow_log_smul_isotypicProj_mem R p hp hR _ h0 hadd hs hM A B j (hj.trans (min_le_left _ _)) f hf⟩

end Formalism.CountingSumsFrames
