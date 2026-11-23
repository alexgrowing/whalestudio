import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.ConstantCoeffRhoOneCanonMonomial

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

instance : DecidablePred (IsLower (n := n)) := fun a => inferInstanceAs (Decidable (a.2 < a.1))
instance : DecidablePred (IsUpper (n := n)) := fun a => inferInstanceAs (Decidable (a.1 < a.2))
instance : DecidablePred (IsDiag (n := n)) := fun a => inferInstanceAs (Decidable (a.1 = a.2))

def allL (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)

def lowL (n : ℕ) : List (Fin n × Fin n) := (allL n).filter fun a => decide (a.2 < a.1)

def diagL (n : ℕ) : List (Fin n × Fin n) := (allL n).filter fun a => decide (a.1 = a.2)

def upL (n : ℕ) : List (Fin n × Fin n) := (allL n).filter fun a => decide (a.1 < a.2)

theorem letters_eq_blocks : letters n = lowL n ++ diagL n ++ upL n := rfl

theorem mem_allL (a : Fin n × Fin n) : a ∈ allL n := by
  simp only [allL, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨a.1, a.2, rfl⟩

theorem mem_lowL {a : Fin n × Fin n} : a ∈ lowL n ↔ IsLower a := by
  simp [lowL, mem_allL, IsLower]

theorem mem_diagL {a : Fin n × Fin n} : a ∈ diagL n ↔ IsDiag a := by
  simp [diagL, mem_allL, IsDiag]

theorem mem_upL {a : Fin n × Fin n} : a ∈ upL n ↔ IsUpper a := by
  simp [upL, mem_allL, IsUpper]

theorem nodup_allL : (allL n).Nodup := by
  have := nodup_letters (n := n)
  rw [letters_eq_blocks] at this
  simp only [allL, List.nodup_flatMap]
  refine ⟨fun i _ => (List.nodup_finRange n).map fun j j' h => by simpa using h, ?_⟩
  refine (List.nodup_finRange n).pairwise_of_forall_ne ?_
  intro i _ i' _ hii'
  simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_finRange, true_and]
  rintro _ ⟨j, rfl⟩ ⟨j', h⟩
  exact hii' (congrArg Prod.fst h).symm

def blockW (l : List (Fin n × Fin n)) (m : Fin n × Fin n →₀ ℕ) : List (Fin n × Fin n) :=
  l.flatMap fun a => List.replicate (m a) a

theorem expand_eq_blocks (m : Fin n × Fin n →₀ ℕ) :
    expand m = blockW (lowL n) m ++ blockW (diagL n) m ++ blockW (upL n) m := by
  simp [expand, letters_eq_blocks, blockW, List.flatMap_append]

theorem blockW_congr {l : List (Fin n × Fin n)} {m m' : Fin n × Fin n →₀ ℕ}
    (h : ∀ a ∈ l, m a = m' a) : blockW l m = blockW l m' := by
  unfold blockW
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem blockW_eq_nil {l : List (Fin n × Fin n)} {m : Fin n × Fin n →₀ ℕ}
    (h : ∀ a ∈ l, m a = 0) : blockW l m = [] := by
  rw [blockW_congr (m' := 0) (by simpa using h)]
  simp [blockW]

theorem mem_of_mem_blockW {l : List (Fin n × Fin n)} {m : Fin n × Fin n →₀ ℕ}
    {a : Fin n × Fin n} (ha : a ∈ blockW l m) : a ∈ l ∧ m a ≠ 0 := by
  simp only [blockW, List.mem_flatMap, List.mem_replicate] at ha
  obtain ⟨b, hb, hne, rfl⟩ := ha
  exact ⟨hb, hne⟩

theorem blockW_ne_nil {l : List (Fin n × Fin n)} {m : Fin n × Fin n →₀ ℕ} {a : Fin n × Fin n}
    (ha : a ∈ l) (hm : m a ≠ 0) : blockW l m ≠ [] := by
  intro h
  have : a ∈ blockW l m := by
    simp only [blockW, List.mem_flatMap, List.mem_replicate]
    exact ⟨a, ha, hm, rfl⟩
  rw [h] at this
  simp at this

theorem canon_eq_blocks (m : Fin n × Fin n →₀ ℕ) :
    canon m = word (blockW (lowL n) m) * word (blockW (diagL n) m) * word (blockW (upL n) m) := by
  rw [canon, expand_eq_blocks, word_append, word_append]

def HasUpper (m : Fin n × Fin n →₀ ℕ) : Prop := ∃ a, IsUpper a ∧ m a ≠ 0

def HasLower (m : Fin n × Fin n →₀ ℕ) : Prop := ∃ a, IsLower a ∧ m a ≠ 0

def IsDiagExp (m : Fin n × Fin n →₀ ℕ) : Prop := ∀ a, m a ≠ 0 → IsDiag a

theorem isDiagExp_or (m : Fin n × Fin n →₀ ℕ) : IsDiagExp m ∨ HasUpper m ∨ HasLower m := by
  by_contra h
  simp only [not_or, IsDiagExp, HasUpper, HasLower, not_forall, not_exists, not_and] at h
  obtain ⟨⟨a, ha, hd⟩, hu, hl⟩ := h
  rcases lt_trichotomy a.1 a.2 with h | h | h
  · exact hu a h ha
  · exact hd h
  · exact hl a h ha

theorem not_isDiagExp_of_hasUpper {m : Fin n × Fin n →₀ ℕ} (h : HasUpper m) : ¬ IsDiagExp m := by
  obtain ⟨a, ha, hm⟩ := h
  intro hd
  have := hd a hm
  simp only [IsUpper, IsDiag] at ha this
  rw [this] at ha; exact lt_irrefl _ ha

theorem not_isDiagExp_of_hasLower {m : Fin n × Fin n →₀ ℕ} (h : HasLower m) : ¬ IsDiagExp m := by
  obtain ⟨a, ha, hm⟩ := h
  intro hd
  have := hd a hm
  simp only [IsLower, IsDiag] at ha this
  rw [this] at ha; exact lt_irrefl _ ha

def cartanSet (n : ℕ) : Set (U n) := Set.range fun i : Fin n => e (i, i)

theorem e_diag_commute (i j : Fin n) : e (i, i) * e (j, j) = e (j, j) * e (i, i) := by
  have h := e_mul_sub_mul (i, i) (j, j)
  by_cases hij : i = j
  · subst hij; rfl
  · simp only [hij, Ne.symm hij, if_false, sub_self] at h
    exact sub_eq_zero.1 h

theorem cartanSet_commute : ∀ a ∈ cartanSet n, ∀ b ∈ cartanSet n, a * b = b * a := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact e_diag_commute i j

def cartanSub (n : ℕ) : Subalgebra ℂ (U n) := Algebra.adjoin ℂ (cartanSet n)

instance cartanSub.instIsMulCommutative : IsMulCommutative (cartanSub n) :=
  Algebra.isMulCommutative_adjoin ℂ cartanSet_commute

open scoped IsMulCommutative

noncomputable def hcEmb : MvPolynomial (Fin n) ℂ →ₐ[ℂ] U n :=
  (cartanSub n).val.comp (aeval fun i => (⟨e (i, i), Algebra.subset_adjoin (s := cartanSet n) (Set.mem_range_self i)⟩ : cartanSub n))

@[simp] theorem hcEmb_X (i : Fin n) : hcEmb (X i) = e (n := n) (i, i) := by
  simp [hcEmb]

theorem hcEmb_mem_cartanSub (p : MvPolynomial (Fin n) ℂ) : hcEmb p ∈ cartanSub n := by
  simp only [hcEmb, AlgHom.comp_apply]
  exact SetLike.coe_mem _

noncomputable def diagExp (m : Fin n × Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => m (i, i)

@[simp] theorem diagExp_apply (m : Fin n × Fin n →₀ ℕ) (i : Fin n) : diagExp m i = m (i, i) := rfl

theorem e_pow_mem_cartanSub (i : Fin n) (k : ℕ) : e (n := n) (i, i) ^ k ∈ cartanSub n :=
  Subalgebra.pow_mem _ (Algebra.subset_adjoin (s := cartanSet n) (Set.mem_range_self i)) k

theorem word_blockW_diagL (m : Fin n × Fin n →₀ ℕ) :
    word (blockW (diagL n) m) = hcEmb (monomial (diagExp m) 1) := by
  classical
  let g : Fin n × Fin n → cartanSub n := fun a =>
    if h : a.1 = a.2 then ⟨e (a.1, a.1), Algebra.subset_adjoin (s := cartanSet n) (Set.mem_range_self a.1)⟩ ^ m a else 1
  have hg : ∀ a ∈ diagL n, ((g a : cartanSub n) : U n) = e a ^ m a := by
    intro a ha
    have h : a.1 = a.2 := mem_diagL.1 ha
    simp only [g, dif_pos h, SubmonoidClass.coe_pow]
    congr 2
    exact Prod.ext rfl h
  have hnodup : (diagL n).Nodup := nodup_allL.filter _
  have hfin : (diagL n).toFinset = Finset.univ.filter fun a : Fin n × Fin n => a.1 = a.2 := by
    ext a; simp [mem_diagL, IsDiag]
  have h1 : word (blockW (diagL n) m) = (((diagL n).map g).prod : cartanSub n) := by
    rw [blockW, word_flatMap_replicate, SubmonoidClass.coe_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun a ha => (hg a ha).symm)
  have h2 : ((diagL n).map g).prod = ∏ i : Fin n, g (i, i) := by
    refine (List.prod_toFinset g hnodup).symm.trans ?_
    rw [hfin, Finset.prod_filter, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp [g]
  rw [h1, h2, hcEmb, AlgHom.comp_apply, aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [Subalgebra.coe_val, diagExp_apply, g]
  rfl

theorem canon_eq_triangular (m : Fin n × Fin n →₀ ℕ) :
    canon m = word (blockW (lowL n) m) * hcEmb (monomial (diagExp m) 1) *
      word (blockW (upL n) m) := by
  rw [canon_eq_blocks, word_blockW_diagL]

def nPlusU (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (u : U n) (a : Fin n × Fin n), IsUpper a ∧ u * e a = x}

def nMinusU (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (u : U n) (a : Fin n × Fin n), IsLower a ∧ e a * u = x}

theorem mul_mem_nPlusU (v : U n) {x : U n} (hx : x ∈ nPlusU n) : v * x ∈ nPlusU n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, a, ha, rfl⟩ := hx
    exact Submodule.subset_span ⟨v * u, a, ha, mul_assoc _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem mem_nMinusU_mul {x : U n} (hx : x ∈ nMinusU n) (v : U n) : x * v ∈ nMinusU n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, a, ha, rfl⟩ := hx
    exact Submodule.subset_span ⟨u * v, a, ha, (mul_assoc _ _ _).symm⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem canon_mem_nPlusU {m : Fin n × Fin n →₀ ℕ} (h : HasUpper m) : canon m ∈ nPlusU n := by
  obtain ⟨a, ha, hm⟩ := h
  have hne := blockW_ne_nil (mem_upL.2 ha) hm
  rw [canon_eq_blocks, ← List.dropLast_append_getLast hne, word_append, word_singleton, ← mul_assoc]
  refine Submodule.subset_span ⟨_, _, ?_, rfl⟩
  exact mem_upL.1 (mem_of_mem_blockW (List.getLast_mem hne)).1

theorem canon_mem_nMinusU {m : Fin n × Fin n →₀ ℕ} (h : HasLower m) : canon m ∈ nMinusU n := by
  obtain ⟨a, ha, hm⟩ := h
  have hne := blockW_ne_nil (mem_lowL.2 ha) hm
  obtain ⟨b, l, hbl⟩ := List.exists_cons_of_ne_nil hne
  rw [canon_eq_blocks, hbl, word_cons, mul_assoc, mul_assoc]
  refine Submodule.subset_span ⟨_, b, ?_, rfl⟩
  have : b ∈ blockW (lowL n) m := by rw [hbl]; exact List.mem_cons_self ..
  exact mem_lowL.1 (mem_of_mem_blockW this).1

noncomputable def notUpper (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  m.filter fun a => ¬ IsUpper a

noncomputable def notLower (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  m.filter fun a => ¬ IsLower a

theorem isUpper_of_mem_support {P : Fin n × Fin n → Prop} {m : Fin n × Fin n →₀ ℕ}
    (hm : ∀ a ∈ m.support, P a) {a : Fin n × Fin n} (ha : ¬ P a) : m a = 0 := by
  by_contra h
  exact ha (hm a (Finsupp.mem_support_iff.2 h))

theorem not_upper_of_lower {a : Fin n × Fin n} (h : IsLower a) : ¬ IsUpper a := by
  simp only [IsLower, IsUpper] at *; exact not_lt.2 h.le

theorem not_upper_of_diag {a : Fin n × Fin n} (h : IsDiag a) : ¬ IsUpper a := by
  simp only [IsDiag, IsUpper] at *; rw [h]; exact lt_irrefl _

theorem not_lower_of_upper {a : Fin n × Fin n} (h : IsUpper a) : ¬ IsLower a := by
  simp only [IsLower, IsUpper] at *; exact not_lt.2 h.le

theorem not_lower_of_diag {a : Fin n × Fin n} (h : IsDiag a) : ¬ IsLower a := by
  simp only [IsDiag, IsLower] at *; rw [h]; exact lt_irrefl _

theorem canon_notUpper_add {m m' : Fin n × Fin n →₀ ℕ} (hm' : ∀ a ∈ m'.support, IsUpper a) :
    word (blockW (lowL n) m) * word (blockW (diagL n) m) * canon m' = canon (notUpper m + m') := by
  have hlow : ∀ a ∈ lowL n, m' a = 0 := fun a ha =>
    isUpper_of_mem_support hm' (not_upper_of_lower (mem_lowL.1 ha))
  have hdiag : ∀ a ∈ diagL n, m' a = 0 := fun a ha =>
    isUpper_of_mem_support hm' (not_upper_of_diag (mem_diagL.1 ha))
  rw [canon_eq_blocks m', blockW_eq_nil hlow, blockW_eq_nil hdiag, canon_eq_blocks (notUpper m + m')]
  simp only [word_nil, one_mul]
  congr 2
  · refine congrArg word (blockW_congr fun a ha => ?_)
    have h := mem_lowL.1 ha
    simp [notUpper, not_upper_of_lower h, hlow a ha]
  · refine congrArg word (blockW_congr fun a ha => ?_)
    have h := mem_diagL.1 ha
    simp [notUpper, not_upper_of_diag h, hdiag a ha]
  · refine blockW_congr fun a ha => ?_
    have h := mem_upL.1 ha
    simp [notUpper, h]

theorem canon_add_notLower {m m' : Fin n × Fin n →₀ ℕ} (hm' : ∀ a ∈ m'.support, IsLower a) :
    canon m' * word (blockW (diagL n) m) * word (blockW (upL n) m) = canon (m' + notLower m) := by
  have hup : ∀ a ∈ upL n, m' a = 0 := fun a ha =>
    isUpper_of_mem_support hm' (not_lower_of_upper (mem_upL.1 ha))
  have hdiag : ∀ a ∈ diagL n, m' a = 0 := fun a ha =>
    isUpper_of_mem_support hm' (not_lower_of_diag (mem_diagL.1 ha))
  rw [canon_eq_blocks m', blockW_eq_nil hup, blockW_eq_nil hdiag, canon_eq_blocks (m' + notLower m)]
  simp only [word_nil, mul_one]
  congr 2
  · refine congrArg word (blockW_congr fun a ha => ?_)
    have h := mem_lowL.1 ha
    simp [notLower, h]
  · refine congrArg word (blockW_congr fun a ha => ?_)
    have h := mem_diagL.1 ha
    simp [notLower, not_lower_of_diag h, hdiag a ha]
  · refine blockW_congr fun a ha => ?_
    have h := mem_upL.1 ha
    simp [notLower, not_lower_of_upper h, hup a ha]

theorem hasUpper_notUpper_add {m m' : Fin n × Fin n →₀ ℕ} (hm' : ∀ a ∈ m'.support, IsUpper a)
    (hdeg : 1 ≤ m'.degree) : HasUpper (notUpper m + m') := by
  have : m' ≠ 0 := by rintro rfl; simp at hdeg
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 this
  refine ⟨a, hm' a (Finsupp.mem_support_iff.2 ha), ?_⟩
  simp only [Finsupp.add_apply]
  exact fun h => ha (by simp at ha ⊢; omega)

theorem hasLower_add_notLower {m m' : Fin n × Fin n →₀ ℕ} (hm' : ∀ a ∈ m'.support, IsLower a)
    (hdeg : 1 ≤ m'.degree) : HasLower (m' + notLower m) := by
  have : m' ≠ 0 := by rintro rfl; simp at hdeg
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 this
  refine ⟨a, hm' a (Finsupp.mem_support_iff.2 ha), ?_⟩
  simp only [Finsupp.add_apply]
  exact fun h => ha (by simp at ha ⊢; omega)

def spanUpper (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, HasUpper m ∧ canon m = x}

def spanLower (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, HasLower m ∧ canon m = x}

theorem canon_mul_e_mem_spanUpper (m : Fin n × Fin n →₀ ℕ) {a : Fin n × Fin n} (ha : IsUpper a) :
    canon m * e a ∈ spanUpper n := by
  have hw : ∀ b ∈ blockW (upL n) m ++ [a], IsUpper b := by
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact mem_upL.1 (mem_of_mem_blockW hb).1
    · rw [List.mem_singleton.1 hb]; exact ha
  have hspan := word_mem_canonSpan closed_upper _ hw
  rw [List.length_append, List.length_singleton, show min 1 ((blockW (upL n) m).length + 1) = 1 by
    omega] at hspan
  have heq : canon m * e a = word (blockW (lowL n) m) * word (blockW (diagL n) m) *
      word (blockW (upL n) m ++ [a]) := by
    rw [canon_eq_blocks, word_append, word_singleton, mul_assoc]
  rw [heq]
  have : ∀ y ∈ canonSpan IsUpper 1 ((blockW (upL n) m).length + 1),
      word (blockW (lowL n) m) * word (blockW (diagL n) m) * y ∈ spanUpper n := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m', hm', h1, -, rfl⟩ := hx
      rw [canon_notUpper_add hm']
      exact Submodule.subset_span ⟨_, hasUpper_notUpper_add hm' h1, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx
  exact this _ hspan

theorem e_mul_canon_mem_spanLower (m : Fin n × Fin n →₀ ℕ) {a : Fin n × Fin n} (ha : IsLower a) :
    e a * canon m ∈ spanLower n := by
  have hw : ∀ b ∈ a :: blockW (lowL n) m, IsLower b := by
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ha
    · exact mem_lowL.1 (mem_of_mem_blockW hb).1
  have hspan := word_mem_canonSpan closed_lower _ hw
  rw [List.length_cons, show min 1 ((blockW (lowL n) m).length + 1) = 1 by omega] at hspan
  rw [canon_eq_blocks, ← mul_assoc, ← mul_assoc, ← word_cons]
  have : ∀ y ∈ canonSpan IsLower 1 ((blockW (lowL n) m).length + 1),
      y * word (blockW (diagL n) m) * word (blockW (upL n) m) ∈ spanLower n := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m', hm', h1, -, rfl⟩ := hx
      rw [canon_add_notLower hm']
      exact Submodule.subset_span ⟨_, hasLower_add_notLower hm' h1, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, add_mul]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ r hx
  exact this _ hspan

theorem spanUpper_le_nPlusU : spanUpper n ≤ nPlusU n :=
  Submodule.span_le.2 fun _ ⟨_, h, hx⟩ => hx ▸ canon_mem_nPlusU h

theorem spanLower_le_nMinusU : spanLower n ≤ nMinusU n :=
  Submodule.span_le.2 fun _ ⟨_, h, hx⟩ => hx ▸ canon_mem_nMinusU h

theorem nPlusU_le_spanUpper : nPlusU n ≤ spanUpper n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, a, ha, rfl⟩
  have hu : u ∈ Submodule.span ℂ (Set.range (canon (n := n))) := by
    rw [span_canon_eq_top]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; exact canon_mul_e_mem_spanUpper m ha
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem nMinusU_le_spanLower : nMinusU n ≤ spanLower n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, a, ha, rfl⟩
  have hu : u ∈ Submodule.span ℂ (Set.range (canon (n := n))) := by
    rw [span_canon_eq_top]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; exact e_mul_canon_mem_spanLower m ha
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

end GroundTheory.Automorphic.HarishChandra
