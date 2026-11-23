import Mathlib

open Module Function

namespace GlobalTheory

section Defs

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]

structure IsSymplecticFamily (B : LinearMap.BilinForm R M) (e f : ι → M) (d : ι → R) : Prop where
  left_left : ∀ i j, B (e i) (e j) = 0
  right_right : ∀ i j, B (f i) (f j) = 0
  left_right_self : ∀ i, B (e i) (f i) = d i
  left_right_ne : ∀ i j, i ≠ j → B (e i) (f j) = 0

def IsSymplecticBasisOfType (B : LinearMap.BilinForm R M) (b : Basis (ι ⊕ ι) R M) (d : ι → R) :
    Prop :=
  IsSymplecticFamily B (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i)) d

def IsSymplecticBasis (B : LinearMap.BilinForm R M) (b : Basis (ι ⊕ ι) R M) : Prop :=
  IsSymplecticBasisOfType B b fun _ => 1

noncomputable def standardAltForm [Fintype ι] [DecidableEq ι] (d : ι → R) :
    LinearMap.BilinForm R (ι ⊕ ι → R) :=
  Matrix.toBilin' (Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)

theorem standardAltForm_apply [Fintype ι] [DecidableEq ι] (d : ι → R) (x y : ι ⊕ ι → R) :
    standardAltForm d x y =
      ∑ i, d i * (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i)) := by
  simp only [standardAltForm, Matrix.toBilin'_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, Matrix.neg_apply, Matrix.zero_apply]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, zero_add, add_zero, mul_neg, neg_mul,
    mul_ite, ite_mul, Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem isAlt_standardAltForm [Fintype ι] [DecidableEq ι] (d : ι → R) :
    (standardAltForm d).IsAlt := fun x => by
  rw [standardAltForm_apply]
  exact Finset.sum_eq_zero fun i _ => by ring

theorem isSymplecticBasisOfType_standardAltForm [Fintype ι] [DecidableEq ι] (d : ι → R) :
    IsSymplecticBasisOfType (standardAltForm d) (Pi.basisFun R (ι ⊕ ι)) d := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
  · simp [standardAltForm, Matrix.toBilin'_single]
  · simp [standardAltForm, Matrix.toBilin'_single]
  · simp [standardAltForm, Matrix.toBilin'_single]
  · simp [standardAltForm, Matrix.toBilin'_single, hij]

namespace IsSymplecticFamily

variable {B : LinearMap.BilinForm R M} {e f : ι → M} {d : ι → R}

theorem left_right [DecidableEq ι] (h : IsSymplecticFamily B e f d) (i j : ι) :
    B (e i) (f j) = if i = j then d i else 0 := by
  split_ifs with hij
  · subst hij; exact h.left_right_self i
  · exact h.left_right_ne i j hij

theorem right_left [DecidableEq ι] (h : IsSymplecticFamily B e f d) (hB : B.IsAlt) (i j : ι) :
    B (f i) (e j) = if i = j then -d i else 0 := by
  rw [← hB.neg_eq, h.left_right]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem swap (h : IsSymplecticFamily B e f d) (hB : B.IsAlt) : IsSymplecticFamily (-B) f e d where
  left_left i j := by simp [h.right_right]
  right_right i j := by simp [h.left_left]
  left_right_self i := by simp [hB.neg_eq, h.left_right_self]
  left_right_ne i j hij := by simp [hB.neg_eq, h.left_right_ne j i hij.symm]

theorem apply_left_sum [Fintype ι] (h : IsSymplecticFamily B e f d) (c : ι ⊕ ι → R) (k : ι) :
    B (e k) (∑ i, c i • Sum.elim e f i) = c (Sum.inr k) * d k := by
  classical
  simp [Fintype.sum_sum_type, h.left_left, h.left_right]

theorem apply_sum_right [Fintype ι] (h : IsSymplecticFamily B e f d) (c : ι ⊕ ι → R) (k : ι) :
    B (∑ i, c i • Sum.elim e f i) (f k) = c (Sum.inl k) * d k := by
  classical
  simp [Fintype.sum_sum_type, h.right_right, h.left_right]

theorem linearIndependent [Finite ι] [IsDomain R] (h : IsSymplecticFamily B e f d)
    (hd : ∀ i, d i ≠ 0) : LinearIndependent R (Sum.elim e f) := by
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  cases i with
  | inl k =>
    have := h.apply_sum_right c k
    rw [hc] at this
    simpa [hd k] using this.symm
  | inr k =>
    have := h.apply_left_sum c k
    rw [hc] at this
    simpa [hd k] using this.symm

theorem sum {κ : Type*} {e' f' : κ → M} {d' : κ → R} (hB : B.IsAlt)
    (h : IsSymplecticFamily B e f d) (h' : IsSymplecticFamily B e' f' d')
    (h₁ : ∀ i j, B (e i) (e' j) = 0) (h₂ : ∀ i j, B (e i) (f' j) = 0)
    (h₃ : ∀ i j, B (f i) (e' j) = 0) (h₄ : ∀ i j, B (f i) (f' j) = 0) :
    IsSymplecticFamily B (Sum.elim e e') (Sum.elim f f') (Sum.elim d d') where
  left_left
    | .inl i, .inl j => h.left_left i j
    | .inl i, .inr j => h₁ i j
    | .inr i, .inl j => hB.eq_iff.1 (h₁ j i)
    | .inr i, .inr j => h'.left_left i j
  right_right
    | .inl i, .inl j => h.right_right i j
    | .inl i, .inr j => h₄ i j
    | .inr i, .inl j => hB.eq_iff.1 (h₄ j i)
    | .inr i, .inr j => h'.right_right i j
  left_right_self
    | .inl i => h.left_right_self i
    | .inr i => h'.left_right_self i
  left_right_ne
    | .inl i, .inl j, hij => h.left_right_ne i j fun a => hij (congrArg _ a)
    | .inl i, .inr j, _ => h₂ i j
    | .inr i, .inl j, _ => hB.eq_iff.1 (h₃ j i)
    | .inr i, .inr j, hij => h'.left_right_ne i j fun a => hij (congrArg _ a)

end IsSymplecticFamily

end Defs

section Frobenius

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M]

omit [IsDomain R] in

theorem exists_pair_dvd_of_bilinForm (B : LinearMap.BilinForm R M) (N : Submodule R M) :
    ∃ e ∈ N, ∃ f ∈ N, (∀ y ∈ N, B e f ∣ B e y) ∧ (∀ x ∈ N, B e f ∣ B x f) ∧
      (∀ x ∈ N, ∀ y ∈ N, B e y = 0 → B x f = 0 → B e f ∣ B x y) := by
  let S : Set (Ideal R) := {J | ∃ x ∈ N, ∃ y ∈ N, J = Ideal.span {B x y}}
  obtain ⟨J, ⟨e, he, f, hf, rfl⟩, hmax⟩ :=
    (wellFounded_gt (α := Ideal R)).has_min S ⟨_, 0, N.zero_mem, 0, N.zero_mem, rfl⟩
  have key : ∀ s : R, (∀ u v : R, ∃ x ∈ N, ∃ y ∈ N, B x y = u * B e f + v * s) → B e f ∣ s := by
    intro s hs
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.span {B e f, s})).principal
    have hg' : Ideal.span {B e f, s} = Ideal.span {g} := hg
    have : g ∈ Ideal.span {B e f, s} := hg' ▸ Ideal.mem_span_singleton_self g
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 this
    obtain ⟨x, hx, y, hy, hxy⟩ := hs u v
    have h1 : Ideal.span {B e f} ≤ Ideal.span {g} :=
      hg' ▸ Ideal.span_mono (by simp)
    have h2 := hmax (Ideal.span {g}) ⟨x, hx, y, hy, by rw [hxy, huv]⟩
    have h3 : Ideal.span {B e f} = Ideal.span {g} := by
      by_contra hne
      exact h2 (lt_of_le_of_ne h1 hne)
    rw [← Ideal.mem_span_singleton, h3, ← hg']
    exact Ideal.subset_span (by simp)
  refine ⟨e, he, f, hf, fun y hy => key _ fun u v => ?_, fun x hx => key _ fun u v => ?_,
    fun x hx y hy h₁ h₂ => key _ fun u v => ?_⟩
  · exact ⟨e, he, u • f + v • y, N.add_mem (N.smul_mem _ hf) (N.smul_mem _ hy), by simp⟩
  · exact ⟨u • e + v • x, N.add_mem (N.smul_mem _ he) (N.smul_mem _ hx), f, hf, by simp⟩
  · exact ⟨u • e + v • x, N.add_mem (N.smul_mem _ he) (N.smul_mem _ hx), f + y,
      N.add_mem hf hy, by simp [h₁, h₂]⟩

theorem exists_isSymplecticFamily_span_eq [Module.Free R M] [Module.Finite R M]
    {B : LinearMap.BilinForm R M} (hB : B.IsAlt) (N : Submodule R M)
    (hN : ∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0) :
    ∃ (g : ℕ) (e f : Fin g → M) (d : Fin g → R), IsSymplecticFamily B e f d ∧ (∀ i, d i ≠ 0) ∧
      (∀ i j, i ≤ j → d i ∣ d j) ∧ Submodule.span R (Set.range (Sum.elim e f)) = N := by
  revert hN
  refine Submodule.inductionOnRank (Module.Free.chooseBasis R M) (fun N => (∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0) →
    ∃ (g : ℕ) (e f : Fin g → M) (d : Fin g → R), IsSymplecticFamily B e f d ∧ (∀ i, d i ≠ 0) ∧
      (∀ i j, i ≤ j → d i ∣ d j) ∧ Submodule.span R (Set.range (Sum.elim e f)) = N) ?_ N
  intro N ih hN
  by_cases hbot : N = ⊥
  · refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, fun i => i.elim0, ?_⟩
    rw [hbot, Submodule.span_eq_bot]
    rintro _ ⟨i | i, rfl⟩ <;> exact i.elim0
  obtain ⟨e, he, f, hf, h₁, h₂, h₃⟩ := exists_pair_dvd_of_bilinForm B N
  have hd : B e f ≠ 0 := by
    intro h0
    apply hbot
    rw [Submodule.eq_bot_iff]
    intro x hx
    refine hN x hx fun y hy => ?_
    rw [h0] at h₁ h₂ h₃
    exact zero_dvd_iff.1 (h₃ x hx y hy (zero_dvd_iff.1 (h₁ y hy)) (zero_dvd_iff.1 (h₂ x hx)))
  let N' : Submodule R M := N ⊓ (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))
  have hmem : ∀ y, y ∈ N' ↔ y ∈ N ∧ B e y = 0 ∧ B f y = 0 := fun y => Iff.rfl
  have hdec : ∀ y ∈ N, ∃ a b : R, ∃ y' ∈ N', y = a • e + b • f + y' := by
    intro y hy
    obtain ⟨b, hb⟩ := h₁ y hy
    obtain ⟨a, ha⟩ := h₂ y hy
    refine ⟨a, b, y - a • e - b • f, (hmem _).2 ⟨N.sub_mem (N.sub_mem hy (N.smul_mem _ he))
      (N.smul_mem _ hf), ?_, ?_⟩, by abel⟩
    · simp [hb, hB.self_eq_zero, mul_comm]
    · simp [← hB.neg_eq y f, ← hB.neg_eq e f, ha, hB.self_eq_zero, mul_comm]
  obtain ⟨g, e', f', d', hs, hd', hdvd, hspan⟩ := ih N' inf_le_left f hf (by
    intro c y hy hc
    have := congrArg (B e) hc
    simpa [((hmem y).1 hy).2.1, hd] using this) (by
    intro x hx hx0
    refine hN x hx.1 fun y hy => ?_
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y hy
    simp [hx0 y' hy', hB.eq_iff.1 ((hmem x).1 hx).2.1, hB.eq_iff.1 ((hmem x).1 hx).2.2])
  have he' : ∀ i, e' i ∈ N' := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hf' : ∀ i, f' i ∈ N' := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inr i, rfl⟩
  refine ⟨g + 1, Fin.cons e e', Fin.cons f f', Fin.cons (B e f) d', ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (he' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.1]
    · simp [hs.left_left]
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (hf' _)).2.2]
    · simp [hB.eq_iff.1 ((hmem _).1 (hf' _)).2.2]
    · simp [hs.right_right]
  · intro i
    cases i using Fin.cases
    · simp
    · simp [hs.left_right_self]
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact absurd rfl hij
    · simp [((hmem _).1 (hf' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.2]
    · simpa using hs.left_right_ne _ _ fun a => hij (congrArg _ a)
  · intro i
    cases i using Fin.cases
    · simpa using hd
    · simpa using hd' _
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact dvd_rfl
    · simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hs.left_right_self]
      exact h₃ _ (he' _).1 _ (hf' _).1 ((hmem _).1 (hf' _)).2.1
        (hB.eq_iff.1 ((hmem _).1 (he' _)).2.2)
    · exact absurd hij (by simp)
    · simpa using hdvd _ _ (by simpa using hij)
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i | i, rfl⟩ <;> cases i using Fin.cases
      · exact he
      · exact (he' _).1
      · exact hf
      · exact (hf' _).1
    · intro y hy
      obtain ⟨a, b, y', hy', rfl⟩ := hdec y hy
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
        (Submodule.smul_mem _ _ ?_)) ?_
      · exact Submodule.subset_span ⟨Sum.inl 0, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inr 0, rfl⟩
      · rw [← hspan] at hy'
        refine Submodule.span_mono ?_ hy'
        rintro _ ⟨i | i, rfl⟩
        · exact ⟨Sum.inl i.succ, rfl⟩
        · exact ⟨Sum.inr i.succ, rfl⟩

end Frobenius

section BasisLemmas

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {B : LinearMap.BilinForm R M}

namespace IsSymplecticBasisOfType

variable {b : Basis (ι ⊕ ι) R M} {d : ι → R}

theorem elim_eq (b : Basis (ι ⊕ ι) R M) :
    Sum.elim (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i)) = b := by
  funext i; cases i <;> rfl

theorem apply_left [Finite ι] (h : IsSymplecticBasisOfType B b d) (x : M) (k : ι) :
    B (b (Sum.inl k)) x = b.repr x (Sum.inr k) * d k := by
  have := Fintype.ofFinite ι
  have h' := IsSymplecticFamily.apply_left_sum h (b.repr x) k
  rwa [elim_eq, b.sum_repr] at h'

theorem apply_right [Finite ι] (h : IsSymplecticBasisOfType B b d) (x : M) (k : ι) :
    B x (b (Sum.inr k)) = b.repr x (Sum.inl k) * d k := by
  have := Fintype.ofFinite ι
  have h' := IsSymplecticFamily.apply_sum_right h (b.repr x) k
  rwa [elim_eq, b.sum_repr] at h'

theorem apply_eq_sum [Fintype ι] (h : IsSymplecticBasisOfType B b d) (hB : B.IsAlt) (x y : M) :
    B x y = ∑ i, d i * (b.repr x (Sum.inl i) * b.repr y (Sum.inr i) -
      b.repr x (Sum.inr i) * b.repr y (Sum.inl i)) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [Fintype.sum_sum_type, map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, h.apply_left,
    ← hB.neg_eq y (b (Sum.inr _)), h.apply_right]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem toMatrix_eq [Fintype ι] [DecidableEq ι] (h : IsSymplecticBasisOfType B b d)
    (hB : B.IsAlt) : LinearMap.BilinForm.toMatrix b B =
      Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0 := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply]
  rcases i with i | i <;> rcases j with j | j
  · simpa using IsSymplecticFamily.left_left h i j
  · simpa [Matrix.diagonal_apply] using IsSymplecticFamily.left_right h i j
  · have := IsSymplecticFamily.right_left h hB i j
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.diagonal_apply]
    rw [this]
    split_ifs <;> simp
  · simpa using IsSymplecticFamily.right_right h i j

theorem swap (h : IsSymplecticBasisOfType B b d) (hB : B.IsAlt) :
    IsSymplecticBasisOfType (-B) (b.reindex (Equiv.sumComm ι ι)) d := by
  simpa [IsSymplecticBasisOfType] using IsSymplecticFamily.swap h hB

theorem reindex {κ : Type*} (h : IsSymplecticBasisOfType B b d) (σ : ι ≃ κ) :
    IsSymplecticBasisOfType B (b.reindex (σ.sumCongr σ)) fun k => d (σ.symm k) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
  · simpa using IsSymplecticFamily.left_left h _ _
  · simpa using IsSymplecticFamily.right_right h _ _
  · simpa using IsSymplecticFamily.left_right_self h _
  · simpa using IsSymplecticFamily.left_right_ne h _ _ (σ.symm.injective.ne hij)

theorem isUnit [Finite ι] (h : IsSymplecticBasisOfType B b d) (hp : Surjective B) (k : ι) :
    IsUnit (d k) := by
  obtain ⟨x, hx⟩ := hp (b.coord (Sum.inr k))
  have := h.apply_right x k
  rw [hx] at this
  simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same] at this
  exact IsUnit.of_mul_eq_one_right _ this.symm

theorem finrank_eq [Fintype ι] [StrongRankCondition R] (b : Basis (ι ⊕ ι) R M) :
    finrank R M = 2 * Fintype.card ι := by
  rw [finrank_eq_card_basis b, Fintype.card_sum, two_mul]

end IsSymplecticBasisOfType

namespace IsSymplecticBasis

variable {b : Basis (ι ⊕ ι) R M}

theorem left_left (h : IsSymplecticBasis B b) (i j : ι) :
    B (b (Sum.inl i)) (b (Sum.inl j)) = 0 := IsSymplecticFamily.left_left h i j

theorem right_right (h : IsSymplecticBasis B b) (i j : ι) :
    B (b (Sum.inr i)) (b (Sum.inr j)) = 0 := IsSymplecticFamily.right_right h i j

theorem left_right [DecidableEq ι] (h : IsSymplecticBasis B b) (i j : ι) :
    B (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0 :=
  IsSymplecticFamily.left_right h i j

theorem right_left [DecidableEq ι] (h : IsSymplecticBasis B b) (hB : B.IsAlt) (i j : ι) :
    B (b (Sum.inr i)) (b (Sum.inl j)) = if i = j then -1 else 0 :=
  IsSymplecticFamily.right_left h hB i j

theorem apply_left [Finite ι] (h : IsSymplecticBasis B b) (x : M) (k : ι) :
    B (b (Sum.inl k)) x = b.repr x (Sum.inr k) := by
  simpa using IsSymplecticBasisOfType.apply_left h x k

theorem apply_right [Finite ι] (h : IsSymplecticBasis B b) (x : M) (k : ι) :
    B x (b (Sum.inr k)) = b.repr x (Sum.inl k) := by
  simpa using IsSymplecticBasisOfType.apply_right h x k

theorem apply_eq_sum [Fintype ι] (h : IsSymplecticBasis B b) (hB : B.IsAlt) (x y : M) :
    B x y = ∑ i, (b.repr x (Sum.inl i) * b.repr y (Sum.inr i) -
      b.repr x (Sum.inr i) * b.repr y (Sum.inl i)) := by
  simpa using IsSymplecticBasisOfType.apply_eq_sum h hB x y

theorem toMatrix_eq [Fintype ι] [DecidableEq ι] (h : IsSymplecticBasis B b) (hB : B.IsAlt) :
    LinearMap.BilinForm.toMatrix b B = -Matrix.J ι R := by
  rw [IsSymplecticBasisOfType.toMatrix_eq h hB, Matrix.J, Matrix.fromBlocks_neg]
  simp

theorem swap (h : IsSymplecticBasis B b) (hB : B.IsAlt) :
    IsSymplecticBasis (-B) (b.reindex (Equiv.sumComm ι ι)) :=
  IsSymplecticBasisOfType.swap h hB

theorem reindex {κ : Type*} (h : IsSymplecticBasis B b) (σ : ι ≃ κ) :
    IsSymplecticBasis B (b.reindex (σ.sumCongr σ)) :=
  IsSymplecticBasisOfType.reindex h σ

theorem bijective [Finite ι] (h : IsSymplecticBasis B b) (hB : B.IsAlt) : Bijective B := by
  classical
  have := Fintype.ofFinite ι
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    refine b.ext_elem fun i => ?_
    rcases i with i | i
    · simp [← h.apply_right, hx]
    · simp [← h.apply_left, ← hB.neg_eq x, hx]
  · intro φ
    refine ⟨∑ i, (φ (b (Sum.inr i)) • b (Sum.inl i) - φ (b (Sum.inl i)) • b (Sum.inr i)),
      b.ext fun j => ?_⟩
    rcases j with j | j
    · simp [h.left_left, h.right_left hB]
    · simp [h.right_right, h.left_right]

end IsSymplecticBasis

theorem bijective_standardAltForm_one [Fintype ι] [DecidableEq ι] :
    Bijective (standardAltForm fun _ : ι => (1 : R)) :=
  IsSymplecticBasis.bijective (isSymplecticBasisOfType_standardAltForm _)
    (isAlt_standardAltForm _)

theorem bijective_neg_bilinForm (h : Bijective B) : Bijective (-B) :=
  neg_involutive.bijective.comp h

theorem IsSymplecticFamily.exists_isSymplecticBasis [IsDomain R] [Finite ι] {e f : ι → M}
    {d : ι → R} (h : IsSymplecticFamily B e f d) (hd : ∀ i, d i ≠ 0)
    (hspan : Submodule.span R (Set.range (Sum.elim e f)) = ⊤) (hp : Surjective B) :
    ∃ b : Basis (ι ⊕ ι) R M, IsSymplecticBasis B b ∧ ∀ i, b (Sum.inl i) = e i := by
  let b := Basis.mk (h.linearIndependent hd) hspan.ge
  have hb : IsSymplecticBasisOfType B b d := by
    simpa [IsSymplecticBasisOfType, b] using h
  choose u hu using fun k => hb.isUnit hp k
  refine ⟨b.unitsSMul (Sum.elim 1 fun k => (u k)⁻¹), ⟨fun i j => ?_, fun i j => ?_, fun i => ?_,
    fun i j hij => ?_⟩, fun i => ?_⟩
  · simp [Basis.unitsSMul_apply, b, h.left_left]
  · simp [Basis.unitsSMul_apply, b, h.right_right, Units.smul_def]
  · simp [Basis.unitsSMul_apply, b, h.left_right_self, Units.smul_def, ← hu]
  · simp [Basis.unitsSMul_apply, b, h.left_right_ne i j hij, Units.smul_def]
  · simp [Basis.unitsSMul_apply, b]

end BasisLemmas

section Existence

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Free R M] [Module.Finite R M] {B : LinearMap.BilinForm R M}

theorem exists_isSymplecticBasisOfType (hB : B.IsAlt) (hnd : Injective B) :
    ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) R M) (d : Fin g → R), IsSymplecticBasisOfType B b d ∧
      (∀ i, d i ≠ 0) ∧ ∀ i j, i ≤ j → d i ∣ d j := by
  obtain ⟨g, e, f, d, h, hd, hdvd, hspan⟩ := exists_isSymplecticFamily_span_eq hB ⊤
    fun x _ hx => (injective_iff_map_eq_zero B).1 hnd x (LinearMap.ext fun y => hx y trivial)
  exact ⟨g, Basis.mk (h.linearIndependent hd) hspan.ge, d,
    by simpa [IsSymplecticBasisOfType] using h, hd, hdvd⟩

theorem exists_isSymplecticBasisOfType_pos {M : Type*} [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] {B : LinearMap.BilinForm ℤ M} (hB : B.IsAlt) (hnd : Injective B) :
    ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) ℤ M) (d : Fin g → ℤ), IsSymplecticBasisOfType B b d ∧
      (∀ i, 0 < d i) ∧ ∀ i j, i ≤ j → d i ∣ d j := by
  obtain ⟨g, b, d, h, hd, hdvd⟩ := exists_isSymplecticBasisOfType hB hnd
  have hu : ∀ k, ∃ u : ℤˣ, (u : ℤ) * d k = |d k| := fun k => by
    rcases abs_choice (d k) with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  choose u hu using hu
  refine ⟨g, b.unitsSMul (Sum.elim 1 u), fun k => |d k|, ⟨fun i j => ?_, fun i j => ?_,
    fun i => ?_, fun i j hij => ?_⟩, fun i => abs_pos.2 (hd i), fun i j hij => by
      simpa using hdvd i j hij⟩
  · simp [Basis.unitsSMul_apply, IsSymplecticFamily.left_left h]
  · simp [Basis.unitsSMul_apply, IsSymplecticFamily.right_right h, Units.smul_def]
  · simp [Basis.unitsSMul_apply, IsSymplecticFamily.left_right_self h, Units.smul_def, hu]
  · simp [Basis.unitsSMul_apply, IsSymplecticFamily.left_right_ne h i j hij, Units.smul_def]

theorem exists_isSymplecticBasis (hB : B.IsAlt) (hp : Bijective B) :
    ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) R M), IsSymplecticBasis B b := by
  obtain ⟨g, e, f, d, h, hd, -, hspan⟩ := exists_isSymplecticFamily_span_eq hB ⊤
    fun x _ hx => (injective_iff_map_eq_zero B).1 hp.1 x (LinearMap.ext fun y => hx y trivial)
  obtain ⟨b, hb, -⟩ := h.exists_isSymplecticBasis hd hspan hp.2
  exact ⟨g, b, hb⟩

theorem exists_isSymplecticBasis_of_finrank (hB : B.IsAlt) (hp : Bijective B) {g : ℕ}
    (hg : finrank R M = 2 * g) : ∃ b : Basis (Fin g ⊕ Fin g) R M, IsSymplecticBasis B b := by
  obtain ⟨g', b, hb⟩ := exists_isSymplecticBasis hB hp
  have := IsSymplecticBasisOfType.finrank_eq b
  obtain rfl : g' = g := by rw [hg, Fintype.card_fin] at this; omega
  exact ⟨b, hb⟩

end Existence

section Isotropic

section Maps

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def quotientOrthogonalToDual (B : LinearMap.BilinForm R M) (hB : B.IsAlt) (I : Submodule R M) :
    (M ⧸ B.orthogonal I) →ₗ[R] Dual R I :=
  (B.orthogonal I).liftQ (I.dualRestrict ∘ₗ B) fun _ hy =>
    LinearMap.ext fun x => hB.eq_iff.1 (hy x x.2)

@[simp]
theorem quotientOrthogonalToDual_mk (B : LinearMap.BilinForm R M) (hB : B.IsAlt)
    (I : Submodule R M) (y : M) (x : I) :
    quotientOrthogonalToDual B hB I (Submodule.Quotient.mk y) x = B y x := rfl

def orthogonalQuotientForm (B : LinearMap.BilinForm R M) (hB : B.IsAlt) (I : Submodule R M) :
    LinearMap.BilinForm R (B.orthogonal I ⧸ I.submoduleOf (B.orthogonal I)) :=
  LinearMap.liftQ₂ _ _ (B.restrict (B.orthogonal I))
    (fun x hx => LinearMap.ext fun y => y.2 x hx)
    (fun x hx => LinearMap.ext fun y => hB.eq_iff.1 (y.2 x hx))

@[simp]
theorem orthogonalQuotientForm_mk (B : LinearMap.BilinForm R M) (hB : B.IsAlt)
    (I : Submodule R M) (x y : B.orthogonal I) :
    orthogonalQuotientForm B hB I (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      B x y := rfl

theorem isTorsionFree_quotient_iff [IsDomain R] (I : Submodule R M) :
    IsTorsionFree R (M ⧸ I) ↔ ∀ (r : R) (x : M), r ≠ 0 → r • x ∈ I → x ∈ I := by
  rw [isTorsionFree_iff_smul_eq_zero]
  constructor
  · intro h r x hr hx
    have := h r (Submodule.Quotient.mk x)
      (by rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hx)
    simpa [hr] using this
  · intro h r x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    by_cases hr : r = 0
    · exact Or.inl hr
    · exact Or.inr ((Submodule.Quotient.mk_eq_zero _).2 (h r x hr hx))

theorem isTorsionFree_quotient_orthogonal [IsDomain R] (B : LinearMap.BilinForm R M)
    (I : Submodule R M) : IsTorsionFree R (M ⧸ B.orthogonal I) :=
  (isTorsionFree_quotient_iff _).2 fun r x hr hx n hn => by
    simpa [hr] using hx n hn

end Maps

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Finite R M] {B : LinearMap.BilinForm R M} {I : Submodule R M}

theorem exists_projection_of_isTorsionFree_quotient (hI : IsTorsionFree R (M ⧸ I)) :
    ∃ p : M →ₗ[R] I, ∀ x : I, p x = x := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property I.mkQ LinearMap.id I.mkQ_surjective
  have hs' : ∀ y, I.mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  refine ⟨LinearMap.codRestrict I (LinearMap.id - s ∘ₗ I.mkQ) fun x => ?_, fun x => ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs',
      sub_self]
  · ext
    simp [(Submodule.Quotient.mk_eq_zero I).2 x.2]

theorem dualRestrict_surjective_of_isTorsionFree_quotient (hI : IsTorsionFree R (M ⧸ I)) :
    Surjective I.dualRestrict := by
  obtain ⟨p, hp⟩ := exists_projection_of_isTorsionFree_quotient hI
  exact fun φ => ⟨φ ∘ₗ p, LinearMap.ext fun x => by simp [hp]⟩

theorem orthogonal_orthogonal_of_isTorsionFree_quotient (hB : B.IsAlt) (hp : Surjective B)
    (hI : IsTorsionFree R (M ⧸ I)) : B.orthogonal (B.orthogonal I) = I := by
  refine le_antisymm (fun x hx => ?_) (LinearMap.BilinForm.le_orthogonal_orthogonal hB.isRefl)
  rw [← Submodule.Quotient.mk_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff R _).1 fun φ => ?_
  obtain ⟨y, hy⟩ := hp (φ ∘ₗ I.mkQ)
  have := hx y fun n hn => hB.eq_iff.1 (by
    rw [hy]; simp [(Submodule.Quotient.mk_eq_zero I).2 hn])
  rwa [hy] at this

theorem exists_isSymplecticFamily_of_isotropic {ι : Type*} [Finite ι] (hB : B.IsAlt)
    (hp : Surjective B) (hI : IsTorsionFree R (M ⧸ I)) (hiso : I ≤ B.orthogonal I)
    (v : Basis ι R I) : ∃ f : ι → M, IsSymplecticFamily B (fun i => (v i : M)) f fun _ => 1 := by
  classical
  have := Fintype.ofFinite ι
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hvv : ∀ i j, B (v i) (v j) = 0 := fun i j => hiso (v j).2 _ (v i).2
  have : ∀ i, ∃ y : M, ∀ j, B (v j) y = if j = i then 1 else 0 := fun i => by
    obtain ⟨ψ, hψ⟩ := dualRestrict_surjective_of_isTorsionFree_quotient hI (v.coord i)
    obtain ⟨y, rfl⟩ := hp ψ
    refine ⟨-y, fun j => ?_⟩
    have := LinearMap.congr_fun hψ (v j)
    rw [Submodule.dualRestrict_apply] at this
    rw [map_neg, hB.neg_eq, this]
    simp [Finsupp.single_apply]
  choose y hy using this
  have hy' : ∀ i j, B (y i) (v j) = if j = i then -1 else 0 := fun i j => by
    rw [← hB.neg_eq, hy]; split_ifs <;> simp
  refine ⟨fun i => y i - ∑ j, (if i < j then B (y i) (y j) else 0) • (v j : M), hvv,
    fun i k => ?_, fun i => ?_, fun i k hik => ?_⟩
  · simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hvv, hy, hy', mul_zero, Finset.sum_const_zero, sub_zero,
      mul_ite, mul_one, mul_neg, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h, h.not_gt]
    · simp [hB.self_eq_zero]
    · simp [h, h.not_gt, ← hB.neg_eq (y i)]
  · simp [hvv, hy, -ite_smul]
  · simp [hvv, hy, hik, -ite_smul]

theorem exists_isSymplecticBasis_extend [Module.Free R M] {ι : Type*} [Finite ι] (hB : B.IsAlt)
    (hp : Bijective B) (hI : IsTorsionFree R (M ⧸ I)) (hiso : I ≤ B.orthogonal I)
    (v : Basis ι R I) :
    ∃ (g : ℕ) (b : Basis ((ι ⊕ Fin g) ⊕ (ι ⊕ Fin g)) R M), IsSymplecticBasis B b ∧
      ∀ i, b (Sum.inl (Sum.inl i)) = v i := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨f, hf⟩ := exists_isSymplecticFamily_of_isotropic hB hp.2 hI hiso v
  let N : Submodule R M := (⨅ i, LinearMap.ker (B (v i))) ⊓ ⨅ i, LinearMap.ker (B (f i))
  have hmem : ∀ y, y ∈ N ↔ (∀ i, B (v i) y = 0) ∧ ∀ i, B (f i) y = 0 := fun y => by
    simp [N, Submodule.mem_iInf]
  have hdec : ∀ y, ∃ a b : ι → R, ∃ y' ∈ N, y = ∑ i, a i • (v i : M) + ∑ i, b i • f i + y' := by
    intro y
    refine ⟨fun i => B y (f i), fun i => B (v i) y,
      y - ∑ i, B y (f i) • (v i : M) - ∑ i, B (v i) y • f i, (hmem _).2 ⟨fun k => ?_, fun k => ?_⟩,
      by abel⟩
    · simp [hf.left_left, hf.left_right]
    · simp [hf.right_right, hf.right_left hB, ← hB.neg_eq y]
  obtain ⟨g, e', f', d, h', hd, -, hspan⟩ := exists_isSymplecticFamily_span_eq hB N (by
    intro x hx hx0
    refine (injective_iff_map_eq_zero B).1 hp.1 x (LinearMap.ext fun y => ?_)
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y
    simp [hx0 y' hy', fun i => hB.eq_iff.1 (((hmem x).1 hx).1 i),
      fun i => hB.eq_iff.1 (((hmem x).1 hx).2 i)])
  have he' : ∀ i, e' i ∈ N := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hf' : ∀ i, f' i ∈ N := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inr i, rfl⟩
  have hs := IsSymplecticFamily.sum hB hf h' (fun i j => ((hmem _).1 (he' j)).1 i)
    (fun i j => ((hmem _).1 (hf' j)).1 i) (fun i j => ((hmem _).1 (he' j)).2 i)
    (fun i j => ((hmem _).1 (hf' j)).2 i)
  obtain ⟨b, hb, hbe⟩ := hs.exists_isSymplecticBasis (by
    rintro (i | i)
    · exact one_ne_zero
    · exact hd i) (by
    rw [eq_top_iff]
    intro y _
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y
    refine Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)) ?_
    · exact Submodule.subset_span ⟨Sum.inl (Sum.inl i), rfl⟩
    · exact Submodule.subset_span ⟨Sum.inr (Sum.inl i), rfl⟩
    · rw [← hspan] at hy'
      refine Submodule.span_mono ?_ hy'
      rintro _ ⟨i | i, rfl⟩
      · exact ⟨Sum.inl (Sum.inr i), rfl⟩
      · exact ⟨Sum.inr (Sum.inr i), rfl⟩) hp.2
  exact ⟨g, b, hb, fun i => hbe _⟩

omit [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R M] in

theorem IsSymplecticBasis.mem_orthogonal_iff {ι κ : Type*} [Finite ι] [Finite κ]
    {b : Basis ((ι ⊕ κ) ⊕ (ι ⊕ κ)) R M} (hb : IsSymplecticBasis B b) {v : Basis ι R I}
    (hv : ∀ i, b (Sum.inl (Sum.inl i)) = v i) (x : M) :
    x ∈ B.orthogonal I ↔ ∀ i, b.repr x (Sum.inr (Sum.inl i)) = 0 := by
  constructor
  · intro hx i
    rw [← hb.apply_left, hv]
    exact hx _ (v i).2
  · intro hx n hn
    have : (B.flip x) ∘ₗ I.subtype = 0 := v.ext fun i => by
      simp [← hv, hb.apply_left, hx]
    exact LinearMap.congr_fun this ⟨n, hn⟩

omit [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R M] in

theorem IsSymplecticBasis.orthogonal_eq_span {ι κ : Type*} [Finite ι] [Finite κ]
    {b : Basis ((ι ⊕ κ) ⊕ (ι ⊕ κ)) R M} (hb : IsSymplecticBasis B b) {v : Basis ι R I}
    (hv : ∀ i, b (Sum.inl (Sum.inl i)) = v i) :
    B.orthogonal I = Submodule.span R
      (Set.range (fun i => b (Sum.inl i)) ∪ Set.range fun k => b (Sum.inr (Sum.inr k))) := by
  have : (Set.range (fun i => b (Sum.inl i)) ∪ Set.range fun k => b (Sum.inr (Sum.inr k))) =
      b '' (Set.range fun i => Sum.inr (Sum.inl i))ᶜ := by
    ext x
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨_, by simp, rfl⟩
      · exact ⟨_, by simp, rfl⟩
    · rintro ⟨i | i | i, hi, rfl⟩
      · exact Or.inl ⟨i, rfl⟩
      · exact absurd ⟨i, rfl⟩ hi
      · exact Or.inr ⟨i, rfl⟩
  ext x
  rw [this, hb.mem_orthogonal_iff hv, Basis.mem_span_image]
  constructor
  · rintro h j hj ⟨i, rfl⟩
    exact Finsupp.mem_support_iff.1 hj (h i)
  · intro h i
    by_contra hne
    exact h (Finsupp.mem_support_iff.2 hne) ⟨i, rfl⟩

end Isotropic

end GlobalTheory
