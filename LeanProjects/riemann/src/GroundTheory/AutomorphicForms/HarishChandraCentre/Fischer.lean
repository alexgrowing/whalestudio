import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.RepBase
import GroundTheory.AutomorphicForms.HarishChandraCentre.FischerForm

namespace GroundTheory.Automorphic.HarishChandra

open MvPolynomial

variable {n : ℕ}

theorem fischer_rowOp (i j : Fin n) (f g : Poly n) :
    fischer (rowOp i j f) g = fischer f (rowOp j i g) := by
  rw [rowOp_apply, rowOp_apply, fischer_sum_left, fischer_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fischer_X_mul, fischer_pderiv]

theorem rowOp_X (i j b c : Fin n) :
    rowOp i j (X (b, c) : Poly n) = if b = j then X (i, c) else 0 := by
  rw [rowOp_apply]
  by_cases hb : b = j
  · subst hb
    rw [if_pos rfl, Finset.sum_eq_single c]
    · rw [pderiv_X_self, mul_one]
    · intro k _ hk
      rw [pderiv_X_of_ne (by intro h; exact hk (Prod.ext_iff.1 h).2.symm), mul_zero]
    · simp
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [pderiv_X_of_ne (by intro h; exact hb (Prod.ext_iff.1 h).1), mul_zero]

noncomputable def rowDer (i j : Fin n) : Derivation ℂ (Poly n) (Poly n) :=
  Derivation.mk' (rowOp i j) fun a b => by
    rw [rowOp_apply, rowOp_apply, rowOp_apply, smul_eq_mul, smul_eq_mul, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring

@[simp] theorem rowDer_coe (i j : Fin n) : (rowDer i j : Module.End ℂ (Poly n)) = rowOp i j := rfl

theorem rowDer_apply (i j : Fin n) (f : Poly n) : rowDer i j f = rowOp i j f := rfl

theorem rowOp_comm_self (a i j : Fin n) :
    rowOp a a * rowOp i j =
      rowOp i j * rowOp a a + ((if i = a then 1 else 0) - (if j = a then 1 else 0) : ℂ) • rowOp i j := by
  have key : ⁅rowDer a a, rowDer i j⁆ =
      ((if i = a then 1 else 0) - (if j = a then 1 else 0) : ℂ) • rowDer i j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨b, c⟩
    rw [Derivation.commutator_apply, Derivation.smul_apply, rowDer_apply, rowDer_apply,
      rowDer_apply, rowDer_apply]
    by_cases hbj : b = j <;> by_cases hba : b = a <;> by_cases hia : i = a <;>
      simp_all [rowOp_X]
  refine LinearMap.ext fun f => ?_
  have h := congrArg (fun D : Derivation ℂ (Poly n) (Poly n) => D f) key
  simp only [Derivation.commutator_apply, Derivation.smul_apply, rowDer_apply] at h
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [← h]
  abel

def rowWt (m : Fin n × Fin n →₀ ℕ) (i : Fin n) : ℕ := ∑ k, m (i, k)

theorem rowOp_self_monomial (i : Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ) :
    rowOp i i (monomial s c) = monomial s (c * (rowWt s i : ℂ)) := by
  rw [rowOp_apply, rowWt, Nat.cast_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_monomial, X, monomial_mul, one_mul]
  by_cases hk : s (i, k) = 0
  · simp [hk]
  · have hle : Finsupp.single (i, k) 1 ≤ s := by
      intro v
      rw [Finsupp.single_apply]
      split_ifs with hv
      · subst hv; omega
      · exact Nat.zero_le _
    rw [add_tsub_cancel_of_le hle]

theorem coeff_rowOp_self (i : Fin n) (m : Fin n × Fin n →₀ ℕ) (f : Poly n) :
    coeff m (rowOp i i f) = (rowWt m i : ℂ) * coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
  | monomial s c =>
    rw [rowOp_self_monomial, coeff_monomial, coeff_monomial]
    by_cases h : s = m
    · subst h; simp [mul_comm]
    · simp [h]

theorem rowWt_eq_of_eigen {h : Poly n} {c : Fin n → ℂ} (hc : ∀ a, rowOp a a h = c a • h)
    {m : Fin n × Fin n →₀ ℕ} (hm : m ∈ h.support) (a : Fin n) : (rowWt m a : ℂ) = c a := by
  have := congrArg (coeff m) (hc a)
  rw [coeff_rowOp_self, coeff_smul, smul_eq_mul] at this
  exact mul_right_cancel₀ (MvPolynomial.mem_support_iff.1 hm) this

noncomputable def wtProj (μ : Fin n → ℕ) : Module.End ℂ (Poly n) where
  toFun f := ∑ m ∈ f.support with rowWt m = μ, monomial m (coeff m f)
  map_add' f g := by
    classical
    ext m
    simp only [coeff_sum, coeff_monomial, coeff_add]
    simp only [Finset.sum_ite_eq', Finset.mem_filter, MvPolynomial.mem_support_iff, coeff_add]
    by_cases hm : rowWt m = μ <;> simp only [hm, and_true, and_false, if_false]
    · by_cases h1 : coeff m f = 0 <;> by_cases h2 : coeff m g = 0 <;> by_cases h3 : coeff m f + coeff m g = 0 <;>
        simp_all
    · simp
  map_smul' c f := by
    classical
    ext m
    simp only [coeff_sum, coeff_monomial, coeff_smul, smul_eq_mul, RingHom.id_apply]
    simp only [Finset.sum_ite_eq', Finset.mem_filter, MvPolynomial.mem_support_iff, coeff_smul,
      smul_eq_mul]
    by_cases hm : rowWt m = μ <;> simp only [hm, and_true, and_false, if_false]
    · by_cases h1 : coeff m f = 0 <;> by_cases h2 : c * coeff m f = 0 <;> simp_all
    · simp

theorem coeff_wtProj (μ : Fin n → ℕ) (m : Fin n × Fin n →₀ ℕ) (f : Poly n) :
    coeff m (wtProj μ f) = if rowWt m = μ then coeff m f else 0 := by
  classical
  change coeff m (∑ m ∈ f.support with rowWt m = μ, monomial m (coeff m f)) = _
  simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter,
    MvPolynomial.mem_support_iff]
  by_cases hm : rowWt m = μ
  · by_cases h1 : coeff m f = 0 <;> simp [hm, h1]
  · simp [hm]

theorem wtProj_eq_self_iff (μ : Fin n → ℕ) (f : Poly n) :
    wtProj μ f = f ↔ ∀ m ∈ f.support, rowWt m = μ := by
  constructor
  · intro h m hm
    by_contra hne
    have := congrArg (coeff m) h
    rw [coeff_wtProj, if_neg hne] at this
    exact MvPolynomial.mem_support_iff.1 hm this.symm
  · intro h
    ext m
    rw [coeff_wtProj]
    split_ifs with hm
    · rfl
    · by_contra hc
      exact hm (h m (MvPolynomial.mem_support_iff.2 (Ne.symm hc)))

theorem wtProj_wtProj (μ ν : Fin n → ℕ) (f : Poly n) :
    wtProj μ (wtProj ν f) = if μ = ν then wtProj ν f else 0 := by
  by_cases h : μ = ν
  · subst h
    rw [if_pos rfl]
    ext m
    rw [coeff_wtProj, coeff_wtProj]
    split_ifs <;> rfl
  · rw [if_neg h]
    ext m
    rw [coeff_wtProj, coeff_wtProj, coeff_zero]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) h
    · rfl
    · rfl

theorem rowOp_self_of_wtProj (μ : Fin n → ℕ) (v : Poly n) (i : Fin n) (h : wtProj μ v = v) :
    rowOp i i v = (μ i : ℂ) • v := by
  ext m
  rw [coeff_rowOp_self, coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ v.support
  · rw [(wtProj_eq_self_iff μ v).1 h m hm]
  · rw [MvPolynomial.notMem_support_iff.1 hm]; simp

theorem wtProj_eq_self_of_eigen {h : Poly n} (ν : Fin n → ℕ)
    (hc : ∀ a, rowOp a a h = (ν a : ℂ) • h) : wtProj ν h = h := by
  rw [wtProj_eq_self_iff]
  intro m hm
  funext a
  exact_mod_cast rowWt_eq_of_eigen hc hm a

theorem sum_wtProj (f : Poly n) : ∑ ν ∈ f.support.image rowWt, wtProj ν f = f := by
  classical
  ext m
  rw [coeff_sum]
  simp only [coeff_wtProj, Finset.sum_ite_eq, Finset.mem_image]
  split_ifs with h
  · rfl
  · by_contra hc
    exact h ⟨m, MvPolynomial.mem_support_iff.2 (Ne.symm hc), rfl⟩

theorem fischer_wtProj (μ : Fin n → ℕ) (f g : Poly n) :
    fischer (wtProj μ f) g = fischer f (wtProj μ g) := by
  classical
  set s := f.support ∪ g.support
  have hg : (wtProj μ g).support ⊆ s := fun m hm => by
    rw [MvPolynomial.mem_support_iff, coeff_wtProj] at hm
    split_ifs at hm
    · exact Finset.mem_union_right _ (MvPolynomial.mem_support_iff.2 hm)
    · exact absurd rfl hm
  rw [fischer_eq_sum _ _ s Finset.subset_union_right, fischer_eq_sum _ _ s hg]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_wtProj, coeff_wtProj]
  split_ifs <;> simp

theorem wtProj_comm {T : Module.End ℂ (Poly n)} (hT : ∀ a, T * rowOp a a = rowOp a a * T)
    (μ : Fin n → ℕ) (f : Poly n) : wtProj μ (T f) = T (wtProj μ f) := by
  classical
  have hν : ∀ ν, wtProj ν (T (wtProj ν f)) = T (wtProj ν f) := fun ν =>
    wtProj_eq_self_of_eigen ν fun a => by
      have h1 := congrArg (fun S : Module.End ℂ (Poly n) => S (wtProj ν f)) (hT a)
      simp only [Module.End.mul_apply] at h1
      rw [← h1, rowOp_self_of_wtProj ν _ a (by rw [wtProj_wtProj, if_pos rfl]), map_smul]
  conv_lhs => rw [← sum_wtProj f, map_sum, map_sum]
  rw [Finset.sum_eq_single μ]
  · exact hν μ
  · intro ν _ hne
    rw [← hν ν, wtProj_wtProj, if_neg (Ne.symm hne)]
  · intro hμ
    have h0 : wtProj μ f = 0 := by
      ext m
      rw [coeff_wtProj, coeff_zero]
      split_ifs with hm
      · by_contra hc
        exact hμ (Finset.mem_image.2 ⟨m, MvPolynomial.mem_support_iff.2 hc, hm⟩)
      · rfl
    rw [h0, map_zero, map_zero]

def wtHeight (μ : Fin n → ℕ) : ℤ := ∑ a, ((n : ℤ) - a) * μ a

theorem rowOp_shift {μ : Fin n → ℕ} {v : Poly n} (hv : wtProj μ v = v) {i j : Fin n} (hij : i < j)
    (hne : rowOp i j v ≠ 0) :
    ∃ μ' : Fin n → ℕ, wtProj μ' (rowOp i j v) = rowOp i j v ∧ ∑ a, μ' a = ∑ a, μ a ∧
      wtHeight μ < wtHeight μ' := by
  classical
  set w := rowOp i j v
  have heig : ∀ a, rowOp a a w =
      ((μ a : ℂ) + ((if i = a then 1 else 0) - (if j = a then 1 else 0))) • w := by
    intro a
    have h1 := congrArg (fun S : Module.End ℂ (Poly n) => S v) (rowOp_comm_self a i j)
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h1
    rw [h1, rowOp_self_of_wtProj μ v a hv, map_smul, add_smul]
  obtain ⟨m, hm⟩ : ∃ m, m ∈ w.support := by
    by_contra h
    push_neg at h
    exact hne (MvPolynomial.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem h))
  have hwt : ∀ m' ∈ w.support, ∀ a, ((rowWt m' a : ℕ) : ℤ) =
      (μ a : ℤ) + ((if i = a then 1 else 0) - (if j = a then 1 else 0)) := by
    intro m' hm' a
    have := rowWt_eq_of_eigen heig hm' a
    have : ((rowWt m' a : ℤ) : ℂ) = (((μ a : ℤ) + ((if i = a then 1 else 0) -
        (if j = a then 1 else 0)) : ℤ) : ℂ) := by
      push_cast; rw [this]
    exact_mod_cast this
  refine ⟨rowWt m, ?_, ?_, ?_⟩
  · rw [wtProj_eq_self_iff]
    intro m' hm'
    funext a
    have h1 := hwt m' hm' a
    have h2 := hwt m hm a
    omega
  · have : ∀ a, ((rowWt m a : ℕ) : ℤ) = (μ a : ℤ) + ((if i = a then 1 else 0) - (if j = a then 1 else 0)) :=
      hwt m hm
    have hs : ((∑ a, rowWt m a : ℕ) : ℤ) = ((∑ a, μ a : ℕ) : ℤ) := by
      push_cast
      rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp
    exact_mod_cast hs
  · have hsum : wtHeight (rowWt m) = wtHeight μ + (((n : ℤ) - i) - ((n : ℤ) - j)) := by
      unfold wtHeight
      simp_rw [hwt m hm]
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast hij
    rw [hsum]
    linarith

theorem eq_zero_of_forall_highestWeight (T T' : Module.End ℂ (Poly n))
    (hcomm : ∀ i j, T * rowOp i j = rowOp i j * T)
    (hadj : ∀ f g, fischer (T f) g = fischer f (T' g))
    (hnormal : T * T' = T' * T)
    (hhw : ∀ (v : Poly n) (μ : Fin n → ℕ), (∀ i j, i < j → rowOp i j v = 0) → wtProj μ v = v →
      T v = 0) : T = 0 := by
  classical

  have hadj' : ∀ f g, fischer (T' f) g = fischer f (T g) := fun f g => by
    rw [← fischer_conj_symm, ← hadj, fischer_conj_symm]

  have hker : ∀ k, T k = 0 → T' k = 0 := by
    intro k hk
    have h1 : fischer (T' k) (T' k) = fischer (T k) (T k) := by
      rw [hadj', hadj]
      have := congrArg (fun S : Module.End ℂ (Poly n) => S k) hnormal
      simp only [Module.End.mul_apply] at this
      rw [this]
    rw [hk, fischer_zero_left] at h1
    exact (fischer_self_eq_zero_iff _).1 h1
  set S : Set (Poly n) := {s | ∀ k, T k = 0 → fischer s k = 0}
  have hS1 : ∀ f, T f ∈ S := fun f k hk => by rw [hadj, hker k hk, fischer_zero_right]
  have hS2 : ∀ μ, ∀ s ∈ S, wtProj μ s ∈ S := fun μ s hs k hk => by
    rw [fischer_wtProj]
    refine hs _ ?_
    rw [← wtProj_comm (fun a => hcomm a a), hk, map_zero]
  have hS3 : ∀ i j, ∀ s ∈ S, rowOp i j s ∈ S := fun i j s hs k hk => by
    rw [fischer_rowOp]
    refine hs _ ?_
    have := congrArg (fun S : Module.End ℂ (Poly n) => S k) (hcomm j i)
    simp only [Module.End.mul_apply] at this
    rw [this, hk, map_zero]
  have hS4 : ∀ s ∈ S, T s = 0 → s = 0 := fun s hs hT =>
    (fischer_self_eq_zero_iff s).1 (hs s hT)
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.zero_apply]
  by_contra hg
  set g := T f
  obtain ⟨m₀, hm₀⟩ : ∃ m, m ∈ g.support := by
    by_contra h
    push_neg at h
    exact hg (MvPolynomial.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem h))
  set μ₀ := rowWt m₀
  have hμ₀ : wtProj μ₀ g ≠ 0 := by
    intro h
    have := congrArg (coeff m₀) h
    rw [coeff_wtProj, if_pos rfl, coeff_zero] at this
    exact MvPolynomial.mem_support_iff.1 hm₀ this
  set d := ∑ a, μ₀ a
  set W : Finset (Fin n → ℕ) :=
    ((Finset.univ : Finset (Fin n → Fin (d + 1))).image fun μ i => (μ i : ℕ)).filter
      fun μ => ∑ a, μ a = d ∧ ∃ s ∈ S, wtProj μ s ≠ 0
  have hmemW : ∀ μ : Fin n → ℕ, ∑ a, μ a = d → (∃ s ∈ S, wtProj μ s ≠ 0) → μ ∈ W := by
    intro μ hsum hex
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨fun i => ⟨μ i, ?_⟩, Finset.mem_univ _, rfl⟩,
      hsum, hex⟩
    have : μ i ≤ d := hsum ▸ Finset.single_le_sum (fun a _ => Nat.zero_le (μ a)) (Finset.mem_univ i)
    omega
  have hW : W.Nonempty := ⟨μ₀, hmemW μ₀ rfl ⟨g, hS1 f, hμ₀⟩⟩
  obtain ⟨μ, hμW, hμmax⟩ := Finset.exists_max_image W wtHeight hW
  obtain ⟨hμsum, s, hs, hvne⟩ := (Finset.mem_filter.1 hμW).2
  set v := wtProj μ s
  have hvS : v ∈ S := hS2 μ s hs
  have hvv : wtProj μ v = v := by rw [wtProj_wtProj, if_pos rfl]
  have hhwv : ∀ i j, i < j → rowOp i j v = 0 := by
    intro i j hij
    by_contra hne
    obtain ⟨μ', h1, h2, h3⟩ := rowOp_shift hvv hij hne
    have hmem : μ' ∈ W := hmemW μ' (h2.trans hμsum) ⟨rowOp i j v, hS3 i j v hvS, by rw [h1]; exact hne⟩
    exact absurd (hμmax μ' hmem) (not_le.2 h3)
  exact hvne (hS4 v hvS (hhw v μ hhwv hvv))

end GroundTheory.Automorphic.HarishChandra
