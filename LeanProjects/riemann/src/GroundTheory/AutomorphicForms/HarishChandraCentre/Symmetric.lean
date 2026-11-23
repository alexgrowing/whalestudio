import Mathlib

namespace GroundTheory.Automorphic.HarishChandra

open MvPolynomial Finset

variable {n : ℕ}

noncomputable abbrev psumFin (k : Fin n) : MvPolynomial (Fin n) ℂ := psum (Fin n) ℂ ((k : ℕ) + 1)

theorem esymm_mem_adjoin_psum (k : ℕ) (hk : k ≤ n) :
    esymm (Fin n) ℂ k ∈ Algebra.adjoin ℂ (Set.range (psumFin (n := n))) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  set A := Algebra.adjoin ℂ (Set.range (psumFin (n := n)))
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [esymm_zero]; exact A.one_mem
  have hps : ∀ j, 1 ≤ j → j ≤ n → psum (Fin n) ℂ j ∈ A := by
    intro j hj1 hjn
    refine Algebra.subset_adjoin ⟨⟨j - 1, by omega⟩, ?_⟩
    show psum (Fin n) ℂ (j - 1 + 1) = psum (Fin n) ℂ j
    rw [Nat.sub_add_cancel hj1]
  have hsum : (k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k ∈ A := by
    rw [mul_esymm_eq_sum]
    refine A.mul_mem (A.pow_mem (A.neg_mem A.one_mem) _) (A.sum_mem fun a ha => ?_)
    rw [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    exact A.mul_mem (A.mul_mem (A.pow_mem (A.neg_mem A.one_mem) _) (ih a.1 ha.2 (by omega)))
      (hps a.2 (by omega) (by omega))
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have e : esymm (Fin n) ℂ k =
      (k : ℂ)⁻¹ • ((k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k) := by
    rw [← map_natCast (C : ℂ →+* MvPolynomial (Fin n) ℂ) k, smul_eq_C_mul, ← mul_assoc, ← C_mul,
      inv_mul_cancel₀ hk', C_1, one_mul]
  rw [e]
  exact A.smul_mem hsum _

theorem aeval_mem_of_forall_mem {A : Subalgebra ℂ (MvPolynomial (Fin n) ℂ)}
    (f : Fin n → MvPolynomial (Fin n) ℂ) (hf : ∀ i, f i ∈ A) (F : MvPolynomial (Fin n) ℂ) :
    aeval f F ∈ A := by
  induction F using MvPolynomial.induction_on with
  | C r => rw [aeval_C]; exact A.algebraMap_mem r
  | add p q hp hq => rw [map_add]; exact A.add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact A.mul_mem hp (hf i)

theorem mem_adjoin_psum_of_isSymmetric {p : MvPolynomial (Fin n) ℂ} (hp : p.IsSymmetric) :
    p ∈ Algebra.adjoin ℂ (Set.range (psumFin (n := n))) := by
  obtain ⟨F, hF⟩ := esymmAlgHom_fin_surjective ℂ (le_refl n) ⟨p, hp⟩
  have e := congrArg Subtype.val hF
  rw [esymmAlgHom_apply] at e
  have e' : aeval (fun i : Fin n => esymm (Fin n) ℂ ((i : ℕ) + 1)) F = p := e
  rw [← e']
  exact aeval_mem_of_forall_mem _ (fun i => esymm_mem_adjoin_psum _ (by omega)) F

def TopClose (k : ℕ) (a b : MvPolynomial (Fin n) ℂ) : Prop :=
  a.totalDegree ≤ k ∧ b.totalDegree ≤ k ∧ (a = b ∨ (a - b).totalDegree < k)

theorem TopClose.one : TopClose (n := n) 0 1 1 := by
  refine ⟨by simp, by simp, Or.inl rfl⟩

theorem TopClose.mul {k l : ℕ} {a b a' b' : MvPolynomial (Fin n) ℂ} (h : TopClose k a b)
    (h' : TopClose l a' b') : TopClose (k + l) (a * a') (b * b') := by
  obtain ⟨ha, hb, hab⟩ := h
  obtain ⟨ha', hb', hab'⟩ := h'
  refine ⟨(totalDegree_mul _ _).trans (add_le_add ha ha'),
    (totalDegree_mul _ _).trans (add_le_add hb hb'), ?_⟩
  by_cases e : a = b ∧ a' = b'
  · left; rw [e.1, e.2]
  right
  have key : a * a' - b * b' = (a - b) * a' + b * (a' - b') := by ring
  rw [key]
  refine lt_of_le_of_lt (totalDegree_add _ _) (max_lt ?_ ?_)
  · rcases hab with h1 | h1
    · rw [h1, sub_self, zero_mul, totalDegree_zero]
      rcases hab' with h2 | h2
      · exact absurd ⟨h1, h2⟩ e
      · omega
    · exact lt_of_le_of_lt (totalDegree_mul _ _) (by omega)
  · rcases hab' with h1 | h1
    · rw [h1, sub_self, mul_zero, totalDegree_zero]
      rcases hab with h2 | h2
      · exact absurd ⟨h2, h1⟩ e
      · omega
    · exact lt_of_le_of_lt (totalDegree_mul _ _) (by omega)

theorem TopClose.pow {k : ℕ} {a b : MvPolynomial (Fin n) ℂ} (h : TopClose k a b) (c : ℕ) :
    TopClose (c * k) (a ^ c) (b ^ c) := by
  induction c with
  | zero => simpa using TopClose.one
  | succ c ih =>
    rw [pow_succ, pow_succ, Nat.succ_mul]
    exact ih.mul h

theorem TopClose.prod {ι : Type*} (s : Finset ι) (k : ι → ℕ) (a b : ι → MvPolynomial (Fin n) ℂ)
    (h : ∀ i ∈ s, TopClose (k i) (a i) (b i)) :
    TopClose (∑ i ∈ s, k i) (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TopClose.one
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, sum_insert hi]
    exact (h i (mem_insert_self _ _)).mul (ih fun j hj => h j (mem_insert_of_mem hj))

theorem isHomogeneous_psum (k : ℕ) : (psum (Fin n) ℂ k).IsHomogeneous k := by
  unfold psum
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i k

def psumWt (c : Fin n →₀ ℕ) : ℕ := ∑ i ∈ c.support, c i * ((i : ℕ) + 1)

theorem symmetric_le_adjoin (q : Fin n → MvPolynomial (Fin n) ℂ) (hq : ∀ k, (q k).IsSymmetric)
    (hdeg : ∀ k, (q k - psum (Fin n) ℂ ((k : ℕ) + 1)).totalDegree < (k : ℕ) + 1) (d : ℕ) :
    ∀ p : MvPolynomial (Fin n) ℂ, p.IsSymmetric → p.totalDegree ≤ d →
      p ∈ Algebra.adjoin ℂ (Set.range q) := by
  set B := Algebra.adjoin ℂ (Set.range q)
  have hBsym : ∀ r ∈ B, r.IsSymmetric := by
    have : B ≤ symmetricSubalgebra (Fin n) ℂ :=
      Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact hq k)
    exact fun r hr => this hr
  have hclose : ∀ i : Fin n, TopClose ((i : ℕ) + 1) (psumFin i) (q i) := by
    intro i
    have h1 : (psumFin i).totalDegree ≤ (i : ℕ) + 1 :=
      (isHomogeneous_psum _).totalDegree_le
    refine ⟨h1, ?_, Or.inr ?_⟩
    · have : q i = psumFin i + (q i - psumFin i) := by ring
      rw [this]
      exact (totalDegree_add _ _).trans (max_le h1 (hdeg i).le)
    · rw [← neg_sub, totalDegree_neg]; exact hdeg i
  induction d with
  | zero =>
    intro p _ hp
    rw [totalDegree_eq_zero_iff_eq_C.1 (show p.totalDegree = 0 by omega)]
    exact B.algebraMap_mem _
  | succ d ih =>
    intro p hp hpd
    obtain ⟨F, rfl⟩ : ∃ F, aeval psumFin F = p := by
      have := mem_adjoin_psum_of_isSymmetric hp
      rw [Algebra.adjoin_range_eq_range_aeval] at this
      exact this
    set P : (Fin n →₀ ℕ) → MvPolynomial (Fin n) ℂ := fun c => c.prod fun i k => psumFin i ^ k
    set Q : (Fin n →₀ ℕ) → MvPolynomial (Fin n) ℂ := fun c => c.prod fun i k => q i ^ k
    have hPhom : ∀ c, (P c).IsHomogeneous (psumWt c) := by
      intro c
      simp only [P, Finsupp.prod, psumWt]
      refine IsHomogeneous.prod _ _ _ fun i _ => ?_
      rw [mul_comm]
      exact (isHomogeneous_psum _).pow _
    have hPQ : ∀ c, TopClose (psumWt c) (P c) (Q c) := by
      intro c
      simp only [P, Q, Finsupp.prod, psumWt]
      exact TopClose.prod _ _ _ _ fun i _ => (hclose i).pow (c i)
    have hF : aeval psumFin F = ∑ c ∈ F.support, coeff c F • P c := by
      conv_lhs => rw [F.as_sum]
      rw [map_sum]
      refine sum_congr rfl fun c _ => ?_
      rw [aeval_monomial, Algebra.smul_def]
    set S := F.support.filter fun c => psumWt c = d + 1
    set r := ∑ c ∈ S, coeff c F • Q c
    have hr : r ∈ B := by
      refine B.sum_mem fun c _ => B.smul_mem ?_ _
      simp only [Q, Finsupp.prod]
      exact B.prod_mem fun i _ => B.pow_mem (Algebra.subset_adjoin ⟨i, rfl⟩) _
    have htop : homogeneousComponent (d + 1) (aeval psumFin F) = ∑ c ∈ S, coeff c F • P c := by
      rw [hF, map_sum, sum_filter]
      refine sum_congr rfl fun c _ => ?_
      rw [map_smul, homogeneousComponent_of_mem (hPhom c)]
      by_cases h : psumWt c = d + 1
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h, smul_zero]
    have hlow : (aeval psumFin F - homogeneousComponent (d + 1) (aeval psumFin F)).totalDegree ≤ d := by
      set p := aeval psumFin F
      rw [totalDegree, Finset.sup_le_iff]
      intro m hm
      rw [mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hm
      have hm' : m ∈ p.support := by
        rw [mem_support_iff]; intro h0; rw [h0] at hm; simp at hm
      have h1 := le_totalDegree hm'
      by_cases hd : m.degree = d + 1
      · rw [if_pos hd, sub_self] at hm; exact absurd rfl hm
      · have : (m.sum fun _ e => e) = m.degree := by
          rfl
        rw [this] at h1 ⊢
        omega
    have hdiff : (∑ c ∈ S, coeff c F • P c - r).totalDegree ≤ d := by
      rw [← sum_sub_distrib]
      refine totalDegree_finsetSum_le fun c hc => ?_
      rw [← smul_sub]
      refine (totalDegree_smul_le _ _).trans ?_
      have hwc : psumWt c = d + 1 := (mem_filter.1 hc).2
      rcases (hPQ c).2.2 with h | h
      · rw [h, sub_self, totalDegree_zero]; exact Nat.zero_le _
      · rw [hwc] at h; omega
    have hkey : (aeval psumFin F - r).totalDegree ≤ d := by
      have : aeval psumFin F - r = (aeval psumFin F - homogeneousComponent (d + 1) (aeval psumFin F))
          + (∑ c ∈ S, coeff c F • P c - r) := by rw [htop]; ring
      rw [this]
      exact (totalDegree_add _ _).trans (max_le hlow hdiff)
    have hsym : (aeval psumFin F - r).IsSymmetric :=
      (symmetricSubalgebra (Fin n) ℂ).sub_mem hp (hBsym r hr)
    have := B.add_mem (ih _ hsym hkey) hr
    rwa [sub_add_cancel] at this

theorem adjoin_eq_symmetricSubalgebra (q : Fin n → MvPolynomial (Fin n) ℂ)
    (hq : ∀ k, (q k).IsSymmetric)
    (hdeg : ∀ k, (q k - psum (Fin n) ℂ ((k : ℕ) + 1)).totalDegree < (k : ℕ) + 1) :
    Algebra.adjoin ℂ (Set.range q) = symmetricSubalgebra (Fin n) ℂ := by
  apply le_antisymm
  · exact Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact hq k)
  · intro p hp
    exact symmetric_le_adjoin q hq hdeg _ p hp le_rfl

end GroundTheory.Automorphic.HarishChandra
