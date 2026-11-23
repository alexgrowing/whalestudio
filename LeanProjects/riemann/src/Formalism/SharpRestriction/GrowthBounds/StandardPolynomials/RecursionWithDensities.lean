import Formalism.SharpRestriction.GrowthBounds.PolBridge

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.PolBridge

section YC

variable {K : Type} [Field K] [CharZero K] {N r : ℕ} [NeZero r]

theorem glAct_mul' (Lt : Letters (Fin N)) (S : Set (Fin N)) (c d : Fin r) (f h : MvPolynomial (Fin N × Fin r) K) :
    glAct K Lt S c d (f * h) = glAct K Lt S c d f * h + f * glAct K Lt S c d h := by
  classical
  unfold glAct
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l ∈ S
  · by_cases hv : Lt.vec l = true
    · simp only [if_pos hl, if_pos hv, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul]
      ring
    · simp only [if_pos hl, if_neg hv, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]
      ring
  · simp only [if_neg hl, LinearMap.zero_apply]
    ring

open Classical in
theorem glAct_X' (Lt : Letters (Fin N)) (S : Set (Fin N)) (c d : Fin r) (a : Fin N) (e : Fin r) :
    glAct K Lt S c d (X (a, e)) =
      if a ∈ S then (if Lt.vec a = true then (if e = d then X (a, c) else 0) else (if e = c then -X (a, d) else 0))
      else 0 := by
  classical
  unfold glAct
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_eq_single a]
  · by_cases hl : a ∈ S
    · by_cases hv : Lt.vec a = true
      · simp only [if_pos hl, if_pos hv, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, pderiv_X]
        by_cases he : e = d
        · subst he; simp
        · have : (a, d) ≠ (a, e) := fun h => he (Prod.mk.inj h).2.symm
          simp [he, Pi.single_apply, Ne.symm this]
      · simp only [if_pos hl, if_neg hv, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          Derivation.coeFn_coe, pderiv_X]
        by_cases he : e = c
        · subst he; simp
        · have : (a, c) ≠ (a, e) := fun h => he (Prod.mk.inj h).2.symm
          simp [he, Pi.single_apply, Ne.symm this]
    · simp only [if_neg hl, LinearMap.zero_apply]
  · intro l _ hla
    have h1 : ∀ b : Fin r, pderiv (l, b) (X (a, e) : MvPolynomial (Fin N × Fin r) K) = 0 := by
      intro b
      rw [pderiv_X, Pi.single_apply, if_neg]
      intro h
      exact hla (Prod.mk.inj h).1.symm
    by_cases hl : l ∈ S
    · by_cases hv : Lt.vec l = true
      · simp only [if_pos hl, if_pos hv, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, h1, mul_zero]
      · simp only [if_pos hl, if_neg hv, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          Derivation.coeFn_coe, h1, mul_zero, neg_zero]
    · simp only [if_neg hl, LinearMap.zero_apply]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem chWt_add (LL : ChainLetters N) (j : ℕ) (c : Fin r) (m m' : Fin N × Fin r →₀ ℕ) :
    chWt LL j c (m + m') = chWt LL j c m + chWt LL j c m' := by
  unfold chWt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Finsupp.add_apply] <;> ring

theorem chWt_single (LL : ChainLetters N) (j : ℕ) (a : Fin N) (e : Fin r) :
    chWt LL j (0 : Fin r) (Finsupp.single (a, e) 1) =
      if (a : ℕ) < j then (if LL.vec a = true then (if e = 0 then 1 else 0) else (if e = 0 then -1 else 0)) else 0 := by
  classical
  unfold chWt
  rw [Finset.sum_eq_single a]
  · by_cases he : e = 0
    · subst he; simp
    · have : (a, e) ≠ (a, (0 : Fin r)) := fun h => he (Prod.mk.inj h).2
      simp [he, Finsupp.single_apply, this]
  · intro i _ hia
    have : (a, e) ≠ (i, (0 : Fin r)) := fun h => hia (Prod.mk.inj h).1.symm
    simp [Finsupp.single_apply, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem ycond_of_stable (LL : ChainLetters N) (j : ℕ) (M : WithTop ℤ) (V : Submodule K (MvPolynomial (Fin N × Fin r) K))
    (h1 : V ≤ MvPolynomial.restrictSupport K {m | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ M}) (h2 : chStable K LL j V) :
    V ≤ YCond K (r := r) LL j M :=
  le_sSup (show V ∈ {S | S ≤ _ ∧ chStable K LL j S} from ⟨h1, h2⟩)

theorem ycond_mono (LL : ChainLetters N) (j : ℕ) {M M' : WithTop ℤ} (h : M ≤ M') :
    YCond K (r := r) LL j M ≤ YCond K (r := r) LL j M' := by
  refine ycond_of_stable LL j M' _ ?_ (ycond_stable LL j M)
  refine (ycond_le LL j M).trans ?_
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  exact fun m hm => le_trans (hx hm) h

theorem ycond_mul (LL : ChainLetters N) (j : ℕ) (M M' : WithTop ℤ) {f h : MvPolynomial (Fin N × Fin r) K}
    (hf : f ∈ YCond K (r := r) LL j M) (hh : h ∈ YCond K (r := r) LL j M') :
    f * h ∈ YCond K (r := r) LL j (M + M') := by
  classical
  have key : YCond K (r := r) LL j M * YCond K (r := r) LL j M' ≤ YCond K (r := r) LL j (M + M') := by
    refine ycond_of_stable LL j _ _ ?_ ?_
    · refine Submodule.mul_le.2 fun f hf h hh => ?_
      have h1 := ycond_le LL j M hf
      have h2 := ycond_le LL j M' hh
      rw [MvPolynomial.mem_restrictSupport_iff] at h1 h2 ⊢
      intro m hm
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul f h (Finset.mem_coe.1 hm))
      have a1 : ((chWt LL j 0 a : ℤ) : WithTop ℤ) ≤ M := h1 (Finset.mem_coe.2 ha)
      have a2 : ((chWt LL j 0 b : ℤ) : WithTop ℤ) ≤ M' := h2 (Finset.mem_coe.2 hb)
      show ((chWt LL j 0 (a + b) : ℤ) : WithTop ℤ) ≤ M + M'
      rw [chWt_add, WithTop.coe_add]
      exact add_le_add a1 a2
    · intro c d x hx
      refine Submodule.mul_induction_on hx (fun f hf h hh => ?_) (fun x y hx hy => ?_)
      · rw [glAct_mul']
        exact Submodule.add_mem _ (Submodule.mul_mem_mul (ycond_stable LL j M c d f hf) hh)
          (Submodule.mul_mem_mul hf (ycond_stable LL j M' c d h hh))
      · rw [map_add]
        exact Submodule.add_mem _ hx hy
  exact key (Submodule.mul_mem_mul hf hh)

theorem ycond_one (LL : ChainLetters N) (j : ℕ) : (1 : MvPolynomial (Fin N × Fin r) K) ∈ YCond K (r := r) LL j (0 : ℤ) := by
  classical
  have key : Submodule.span K {(1 : MvPolynomial (Fin N × Fin r) K)} ≤ YCond K (r := r) LL j ((0 : ℤ) : WithTop ℤ) := by
    refine ycond_of_stable LL j _ _ ?_ ?_
    · rw [Submodule.span_le]
      rintro _ rfl
      show (1 : MvPolynomial (Fin N × Fin r) K) ∈ MvPolynomial.restrictSupport K _
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro m hm
      have hm' : m = 0 := by
        have := MvPolynomial.mem_support_iff.1 (Finset.mem_coe.1 hm)
        rw [MvPolynomial.coeff_one] at this
        by_contra h
        exact this (if_neg (Ne.symm h))
      subst hm'
      show ((chWt LL j 0 (0 : Fin N × Fin r →₀ ℕ) : ℤ) : WithTop ℤ) ≤ _
      simp [chWt]
    · intro c d x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      have h1 : glAct K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d (1 : MvPolynomial (Fin N × Fin r) K) = 0 := by
        have := glAct_mul' (K := K) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d 1 1
        simp only [mul_one, one_mul] at this
        exact left_eq_add.1 this |>.symm ▸ rfl
      rw [map_smul, h1, smul_zero]
      exact Submodule.zero_mem _
  exact key (Submodule.subset_span rfl)

def vWt (LL : ChainLetters N) (j : ℕ) (a : Fin N) : ℕ := if LL.vec a = true ∧ (a : ℕ) < j then 1 else 0

theorem ycond_X (LL : ChainLetters N) (j : ℕ) (a : Fin N) (e : Fin r) :
    (X (a, e) : MvPolynomial (Fin N × Fin r) K) ∈ YCond K (r := r) LL j ((vWt LL j a : ℤ) : WithTop ℤ) := by
  classical
  have key : Submodule.span K (Set.range fun e' : Fin r => (X (a, e') : MvPolynomial (Fin N × Fin r) K)) ≤
      YCond K (r := r) LL j ((vWt LL j a : ℤ) : WithTop ℤ) := by
    refine ycond_of_stable LL j _ _ ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨e', rfl⟩
      show (X (a, e') : MvPolynomial (Fin N × Fin r) K) ∈ MvPolynomial.restrictSupport K _
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro m hm
      have hm' : m = Finsupp.single (a, e') 1 := by
        have := Finset.mem_coe.1 hm
        rw [MvPolynomial.support_X] at this
        exact Finset.mem_singleton.1 this
      subst hm'
      show ((chWt LL j 0 (Finsupp.single (a, e') 1) : ℤ) : WithTop ℤ) ≤ _
      rw [chWt_single, WithTop.coe_le_coe]
      unfold vWt
      split_ifs <;> simp_all
    · intro c d x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨e', rfl⟩ := hx
        show glAct K _ _ c d (X (a, e')) ∈ _
        rw [glAct_X']
        split_ifs
        · exact Submodule.subset_span ⟨c, rfl⟩
        · exact Submodule.zero_mem _
        · exact Submodule.neg_mem _ (Submodule.subset_span ⟨d, rfl⟩)
        · exact Submodule.zero_mem _
        · exact Submodule.zero_mem _
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul t x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  exact key (Submodule.subset_span ⟨e, rfl⟩)

theorem ycond_pow (LL : ChainLetters N) (j : ℕ) (z : ℤ) {f : MvPolynomial (Fin N × Fin r) K}
    (hf : f ∈ YCond K (r := r) LL j (z : WithTop ℤ)) (n : ℕ) :
    f ^ n ∈ YCond K (r := r) LL j (((n : ℤ) * z : ℤ) : WithTop ℤ) := by
  induction n with
  | zero => simpa using ycond_one (K := K) LL j
  | succ n ih =>
    rw [pow_succ]
    have := ycond_mul LL j _ _ ih hf
    rw [← WithTop.coe_add] at this
    have e : (n : ℤ) * z + z = ((n + 1 : ℕ) : ℤ) * z := by push_cast; ring
    rwa [e] at this

theorem ycond_prod (LL : ChainLetters N) (j : ℕ) {ι : Type} (s : Finset ι) (z : ι → ℤ)
    (f : ι → MvPolynomial (Fin N × Fin r) K) (hf : ∀ i ∈ s, f i ∈ YCond K (r := r) LL j (z i : WithTop ℤ)) :
    ∏ i ∈ s, f i ∈ YCond K (r := r) LL j ((∑ i ∈ s, z i : ℤ) : WithTop ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ycond_one (K := K) LL j
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, WithTop.coe_add]
    exact ycond_mul LL j _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

def tcPairP (K : Type) [CommRing K] {N r : ℕ} (a a' : Fin N) : MvPolynomial (Fin N × Fin r) K := ∑ c, X (a, c) * X (a', c)

def pWt (j : ℕ) (a a' : Fin N) : ℕ := if (a : ℕ) < j ∧ ¬ (a' : ℕ) < j then 1 else 0

theorem ycond_pair (LL : ChainLetters N) (j : ℕ) (a a' : Fin N) (ha : LL.vec a = true) (ha' : LL.vec a' = false) :
    tcPairP K (r := r) a a' ∈ YCond K (r := r) LL j ((pWt j a a' : ℤ) : WithTop ℤ) := by
  classical
  by_cases hboth : (a : ℕ) < j ∧ (a' : ℕ) < j
  · have hp : pWt j a a' = 0 := by unfold pWt; rw [if_neg]; tauto
    rw [hp]
    have key : Submodule.span K {tcPairP K (r := r) a a'} ≤ YCond K (r := r) LL j (((0 : ℕ) : ℤ) : WithTop ℤ) := by
      refine ycond_of_stable LL j _ _ ?_ ?_
      · rw [Submodule.span_le]
        rintro _ rfl
        show tcPairP K (r := r) a a' ∈ MvPolynomial.restrictSupport K _
        refine Submodule.sum_mem _ fun c _ => ?_
        rw [MvPolynomial.mem_restrictSupport_iff]
        intro m hm
        obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul _ _ (Finset.mem_coe.1 hm))
        rw [MvPolynomial.support_X] at hx hy
        rw [Finset.mem_singleton.1 hx, Finset.mem_singleton.1 hy]
        show ((chWt LL j 0 _ : ℤ) : WithTop ℤ) ≤ _
        have hv' : ¬ LL.vec a' = true := by rw [ha']; exact Bool.false_ne_true
        rw [chWt_add, chWt_single, chWt_single, if_pos hboth.1, if_pos hboth.2, if_pos ha, if_neg hv']
        by_cases hc : c = 0 <;> simp [hc]
      · intro c d x hx
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
        have h0 : glAct K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d (tcPairP K (r := r) a a') = 0 := by
          unfold tcPairP
          rw [map_sum]
          simp only [glAct_mul', glAct_X']
          have m1 : a ∈ {i : Fin N | (i : ℕ) < j} := hboth.1
          have m2 : a' ∈ {i : Fin N | (i : ℕ) < j} := hboth.2
          simp only [if_pos m1, if_pos m2, if_pos ha, ha', Bool.false_eq_true, if_false]
          rw [Finset.sum_add_distrib]
          simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        rw [map_smul, h0, smul_zero]
        exact Submodule.zero_mem _
    exact key (Submodule.subset_span rfl)
  · have hle : ((vWt LL j a : ℤ) : WithTop ℤ) + ((vWt LL j a' : ℤ) : WithTop ℤ) ≤ ((pWt j a a' : ℤ) : WithTop ℤ) := by
      rw [← WithTop.coe_add, WithTop.coe_le_coe]
      unfold vWt pWt
      simp only [ha, ha', true_and, Bool.false_eq_true, false_and, if_false]
      split_ifs <;> simp_all
    refine Submodule.sum_mem _ fun c _ => ?_
    exact ycond_mono LL j hle (ycond_mul LL j _ _ (ycond_X LL j a c) (ycond_X LL j a' c))

theorem ycond_monomial (LL : ChainLetters N) (j : ℕ) (ε : Fin N × Fin r →₀ ℕ) :
    (monomial ε (1 : K) : MvPolynomial (Fin N × Fin r) K) ∈
      YCond K (r := r) LL j ((∑ v : Fin N × Fin r, (ε v : ℤ) * (vWt LL j v.1 : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  have e : (monomial ε (1 : K) : MvPolynomial (Fin N × Fin r) K) = ∏ v : Fin N × Fin r, X v ^ ε v := by
    rw [MvPolynomial.monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [e]
  exact ycond_prod LL j Finset.univ _ _ fun v _ => ycond_pow LL j _ (ycond_X LL j v.1 v.2) (ε v)

end YC

end Formalism.MainNotions.ColumnSystems.Pf
