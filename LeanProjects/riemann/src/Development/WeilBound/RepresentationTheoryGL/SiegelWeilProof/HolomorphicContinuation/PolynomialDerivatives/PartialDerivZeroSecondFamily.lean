import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoeffSmulX

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

def pE : (Fin m × Fin n × Bool) ≃ (Fin m × Fin n × Bool) where
  toFun k := (k.1, k.2.1, !k.2.2)
  invFun k := (k.1, k.2.1, !k.2.2)
  left_inv k := by simp
  right_inv k := by simp

@[simp] theorem pE_apply (k : Fin m × Fin n × Bool) : pE k = (k.1, k.2.1, !k.2.2) := rfl

@[simp] theorem pE_pE (k : Fin m × Fin n × Bool) : pE (pE k) = k := by simp

theorem pE_symm : (pE : (Fin m × Fin n × Bool) ≃ (Fin m × Fin n × Bool)).symm = pE := rfl

theorem first_family_partner_iff (ε : Fin m → Bool) (k : Fin m × Fin n × Bool) : inF1 ε (pE k) ↔ ¬ inF1 ε k := by
  obtain ⟨a, i, b⟩ := k; simp only [pE_apply, inF1]; cases b <;> cases ε a <;> simp

theorem mem_first_family_iff (ε : Fin m → Bool) (p : PX m n) : p ∈ F1 ε ↔ ∀ s ∈ p.support, ∀ k ∈ s.support, inF1 ε k := by
  unfold F1
  rw [Subalgebra.mem_toSubmodule, MvPolynomial.mem_supported]
  constructor
  · intro h s hs k hk; exact h (mem_vars k |>.mpr ⟨s, hs, hk⟩)
  · intro h k hk; obtain ⟨s, hs, hk'⟩ := (mem_vars k).mp hk; exact h s hs k hk'

theorem mem_second_family_iff (ε : Fin m → Bool) (p : PX m n) : p ∈ F2 ε ↔ ∀ s ∈ p.support, ∀ k ∈ s.support, ¬ inF1 ε k := by
  unfold F2
  rw [Subalgebra.mem_toSubmodule, MvPolynomial.mem_supported]
  constructor
  · intro h s hs k hk; exact h (mem_vars k |>.mpr ⟨s, hs, hk⟩)
  · intro h k hk; obtain ⟨s, hs, hk'⟩ := (mem_vars k).mp hk; exact h s hs k hk'

theorem pderiv_mem_supported (S : Set (Fin m × Fin n × Bool)) (k) {p : PX m n} (hp : p ∈ supported ℂ S) :
    pderiv k p ∈ supported ℂ S := by
  rw [supported_eq_adjoin_X] at hp ⊢
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, _, rfl⟩ := hx
    rw [pderiv_X]
    by_cases h : k = j
    · subst h; simp [Subalgebra.one_mem]
    · simp [Pi.single_apply, Ne.symm h, h]
  | algebraMap r => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem (Algebra.adjoin_le (fun z hz => Algebra.subset_adjoin hz) hx') hy)
      (mul_mem (Algebra.adjoin_le (fun z hz => Algebra.subset_adjoin hz) hy') hx)

theorem partial_deriv_mem_first_family (ε : Fin m → Bool) (k) {p : PX m n} (hp : p ∈ F1 ε) : pderiv k p ∈ F1 ε :=
  pderiv_mem_supported _ k hp

theorem partial_deriv_mem_second_family (ε : Fin m → Bool) (k) {p : PX m n} (hp : p ∈ F2 ε) : pderiv k p ∈ F2 ε :=
  pderiv_mem_supported _ k hp

theorem variable_mul_mem_first_family (ε : Fin m → Bool) {k} (hk : inF1 ε k) {p : PX m n} (hp : p ∈ F1 ε) : X k * p ∈ F1 ε :=
  Subalgebra.mul_mem _ (MvPolynomial.X_mem_supported.mpr hk) hp

theorem variable_mul_mem_second_family (ε : Fin m → Bool) {k} (hk : ¬ inF1 ε k) {p : PX m n} (hp : p ∈ F2 ε) : X k * p ∈ F2 ε :=
  Subalgebra.mul_mem _ (MvPolynomial.X_mem_supported.mpr hk) hp

theorem partial_deriv_zero_first_family (ε : Fin m → Bool) {k} (hk : ¬ inF1 ε k) {p : PX m n} (hp : p ∈ F1 ε) : pderiv k p = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨s, hs, hks⟩ := (mem_vars k).mp hv
  exact hk ((mem_first_family_iff ε p).mp hp s hs k hks)

theorem partial_deriv_zero_second_family (ε : Fin m → Bool) {k} (hk : inF1 ε k) {p : PX m n} (hp : p ∈ F2 ε) : pderiv k p = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨s, hs, hks⟩ := (mem_vars k).mp hv
  exact (mem_second_family_iff ε p).mp hp s hs k hks hk

def piC (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ :=
  ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false)))

def Bal (s : Fin m × Fin n × Bool →₀ ℕ) : Prop := ∀ a i, s (a, i, false) = s (a, i, true)

instance (s : Fin m × Fin n × Bool →₀ ℕ) : Decidable (Bal s) := by unfold Bal; infer_instance

theorem contr_eqS (c : ℝ) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) {p : PX m n} (hp : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, if Bal s then p.coeff s * piC c s else 0 := by
  unfold contr
  refine Finset.sum_subset hp fun s _ hs => ?_
  have h0 : p.coeff s = 0 := by
    by_contra h; exact hs (MvPolynomial.mem_support_iff.mpr h)
  simp [h0]

theorem contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eqS c (p.support ∪ q.support) MvPolynomial.support_add, contr_eqS c (p.support ∪ q.support) Finset.subset_union_left,
    contr_eqS c (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [coeff_add, add_mul]

theorem contr_smul (c : ℝ) (r : ℂ) (p : PX m n) : contr c (r • p) = r * contr c p := by
  classical
  rw [contr_eqS c p.support MvPolynomial.support_smul, contr_eqS c p.support le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [coeff_smul, mul_assoc]

theorem contr_sum (c : ℝ) {ι : Type} (I : Finset ι) (f : ι → PX m n) : contr c (∑ i ∈ I, f i) = ∑ i ∈ I, contr c (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [contr]
  | insert a I ha ih => rw [Finset.sum_insert ha, contr_add, ih, Finset.sum_insert ha]

theorem contr_neg (c : ℝ) (p : PX m n) : contr c (-p) = -contr c p := by
  rw [show -p = (-1 : ℂ) • p by simp, contr_smul]; ring

theorem contr_sub (c : ℝ) (p q : PX m n) : contr c (p - q) = contr c p - contr c q := by
  rw [sub_eq_add_neg, contr_add, contr_neg]; ring

theorem contr_monomial (c : ℝ) (v : Fin m × Fin n × Bool →₀ ℕ) (d : ℂ) :
    contr c (monomial v d) = if Bal v then d * piC c v else 0 := by
  classical
  rw [contr_eqS c {v} ((support_monomial_subset).trans (by simp)), Finset.sum_singleton]
  simp [coeff_monomial]

theorem bal_iff (ε : Fin m → Bool) {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k)
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) : Bal (s + u) ↔ s = u.mapDomain pE := by
  have hs0 : ∀ k, ¬ inF1 ε k → s k = 0 := fun k hk => by
    by_contra h; exact hk (hs k (Finsupp.mem_support_iff.mpr h))
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  constructor
  · intro hb
    ext ⟨a, i, b⟩
    rw [Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply]
    have hb' := hb a i
    simp only [Finsupp.add_apply] at hb'
    cases b <;> cases hεa : ε a
    · have h1 := hs0 (a, i, false) (by simp [inF1, hεa])
      have h2 := hu0 (a, i, true) (by simp [inF1, hεa])
      simp only [Bool.not_false]; omega
    · have h1 := hu0 (a, i, false) (by simp [inF1, hεa])
      have h2 := hs0 (a, i, true) (by simp [inF1, hεa])
      simp only [Bool.not_false]; omega
    · have h1 := hu0 (a, i, true) (by simp [inF1, hεa])
      have h2 := hs0 (a, i, false) (by simp [inF1, hεa])
      simp only [Bool.not_true]; omega
    · have h1 := hs0 (a, i, true) (by simp [inF1, hεa])
      have h2 := hu0 (a, i, false) (by simp [inF1, hεa])
      simp only [Bool.not_true]; omega
  · intro h a i
    rw [h]
    simp only [Finsupp.add_apply, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_false, Bool.not_true]
    ring

theorem piC_eq_wt (ε : Fin m → Bool) (c : ℝ) {s u : Fin m × Fin n × Bool →₀ ℕ}
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) (h : s = u.mapDomain pE) : piC c (s + u) = (wt c s : ℂ) := by
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  rw [wt_univ]
  push_cast
  rw [Fintype.prod_prod_type]
  unfold piC
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool]
  subst h
  simp only [Finsupp.add_apply, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_false, Bool.not_true]
  cases hεa : ε a
  · have h1 := hu0 (a, i, true) (by simp [inF1, hεa])
    rw [h1]; simp
  · have h1 := hu0 (a, i, false) (by simp [inF1, hεa])
    rw [h1]; simp [mul_comm]

theorem contr_mono (ε : Fin m → Bool) (c : ℝ) {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k)
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) (a b : ℂ) :
    contr c (monomial s a * monomial u b) = if s = u.mapDomain pE then a * b * (wt c s : ℂ) else 0 := by
  rw [monomial_mul, contr_monomial]
  by_cases h : s = u.mapDomain pE
  · rw [if_pos ((bal_iff ε hs hu).mpr h), if_pos h, piC_eq_wt ε c hu h]
  · rw [if_neg (fun hb => h ((bal_iff ε hs hu).mp hb)), if_neg h]

theorem contr_eq_bf (ε : Fin m → Bool) (c : ℝ) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (h * g) = bf (fun s => (wt c s : ℂ)) h (rename pE g) := by
  conv_lhs => rw [h.as_sum, g.as_sum, Finset.sum_mul_sum, contr_sum]
  conv_rhs => rw [h.as_sum, g.as_sum, map_sum, bf_sum_left]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [contr_sum, bf_sum_right]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [contr_mono ε c ((mem_first_family_iff ε h).mp hh s hs) ((mem_second_family_iff ε g).mp hg u hu), rename_monomial, bf_monomial]

theorem T1 (ε : Fin m → Bool) {c : ℝ} {k} (hk : inF1 ε k) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X k * h * g) = ((2 * c : ℝ) : ℂ) * contr c (h * pderiv (pE k) g) := by
  rw [contr_eq_bf ε c (variable_mul_mem_first_family ε hk hh) hg, contr_eq_bf ε c hh (partial_deriv_mem_second_family ε _ hg), bf_X_mul _ (wt_step c)]
  congr 2
  have := pderiv_rename (R := ℂ) (τ := Fin m × Fin n × Bool) (σ := Fin m × Fin n × Bool) pE.injective (pE k) g
  rw [pE_pE] at this
  exact this

theorem T2 (ε : Fin m → Bool) {c : ℝ} {k} (hk : inF1 ε k) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    ((2 * c : ℝ) : ℂ) * contr c (pderiv k h * g) = contr c (h * (X (pE k) * g)) := by
  rw [contr_eq_bf ε c (partial_deriv_mem_first_family ε _ hh) hg,
    contr_eq_bf ε c hh (variable_mul_mem_second_family ε (fun h' => (first_family_partner_iff ε k).mp h' hk) hg), bf_pderiv _ (wt_step c)]
  congr 1
  rw [map_mul, rename_X, pE_pE]

end CoreC

end PositivityTheory.Rg.Sw.LC
