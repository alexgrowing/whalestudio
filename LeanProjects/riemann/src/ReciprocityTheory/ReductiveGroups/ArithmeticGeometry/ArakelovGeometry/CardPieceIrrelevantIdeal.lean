import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqSumMultihomogeneousComponents

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mem_multidegree_piece_iff {W : Ideal (MRing ι)} {a : K → ℕ} {y : MRing ι ⧸ W} :
    y ∈ mPiece W a ↔ ∃ h, IsMultiHomog h a ∧ Ideal.Quotient.mk W h = y := by
  unfold mPiece
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, (mem_mHom_iff _ _).1 hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, (mem_mHom_iff _ _).2 hh, rfl⟩

theorem quotient_mk_mul_congr_colon {F q : Ideal (MRing ι)} {f : MRing ι} (hq : ∀ g, g ∈ q ↔ g * f ∈ F)
    {g g' : MRing ι} (h : Ideal.Quotient.mk q g = Ideal.Quotient.mk q g') :
    Ideal.Quotient.mk F (g * f) = Ideal.Quotient.mk F (g' * f) := by
  rw [Ideal.Quotient.eq] at h ⊢
  rw [← sub_mul]
  exact (hq _).1 h

theorem card_piece_colon_exact {F q : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) {f : MRing ι} {c : K → ℕ}
    (hf : IsMultiHomog f c) (hq : ∀ g, g ∈ q ↔ g * f ∈ F) {a : K → ℕ} (hca : c ≤ a) :
    Nat.card (mPiece F a) =
      Nat.card (mPiece q (a - c)) * Nat.card (mPiece (F ⊔ Ideal.span {f}) a) := by
  have hle : F ≤ F ⊔ Ideal.span {f} := le_sup_left
  let ψ : mPiece F a →+ MRing ι ⧸ (F ⊔ Ideal.span {f}) :=
    (Ideal.Quotient.factor hle).toAddMonoidHom.comp (mPiece F a).subtype.toAddMonoidHom
  have hψ : ∀ y : mPiece F a, ψ y = Ideal.Quotient.factor hle y.1 := fun _ => rfl
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
  have h2 : Nat.card (mPiece F a ⧸ ψ.ker) = Nat.card (mPiece (F ⊔ Ideal.span {f}) a) := by
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    rw [AddMonoidHom.mem_range, mem_multidegree_piece_iff]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨h, hh, hx⟩ := mem_multidegree_piece_iff.1 x.2
      refine ⟨h, hh, ?_⟩
      rw [hψ, ← hx, Ideal.Quotient.factor_mk]
    · rintro ⟨h, hh, rfl⟩
      refine ⟨⟨Ideal.Quotient.mk F h, mem_multidegree_piece_iff.2 ⟨h, hh, rfl⟩⟩, ?_⟩
      rw [hψ, Ideal.Quotient.factor_mk]
  have h3 : Nat.card (mPiece q (a - c)) = Nat.card ψ.ker := by
    let g₀ : MRing ι ⧸ q → MRing ι := fun x => (Ideal.Quotient.mk_surjective x).choose
    have hg₀ : ∀ x, Ideal.Quotient.mk q (g₀ x) = x := fun x =>
      (Ideal.Quotient.mk_surjective x).choose_spec
    have hmem1 : ∀ x : mPiece q (a - c), Ideal.Quotient.mk F (g₀ x.1 * f) ∈ mPiece F a := by
      intro x
      obtain ⟨g, hg, hgx⟩ := mem_multidegree_piece_iff.1 x.2
      refine mem_multidegree_piece_iff.2 ⟨g * f, ?_, quotient_mk_mul_congr_colon hq (by rw [hg₀, hgx])⟩
      have := isMultiHomog_mul' hg hf
      rwa [tsub_add_cancel_of_le hca] at this
    have hmem2 : ∀ x : mPiece q (a - c), (⟨_, hmem1 x⟩ : mPiece F a) ∈ ψ.ker := by
      intro x
      rw [AddMonoidHom.mem_ker, hψ]
      show Ideal.Quotient.factor hle (Ideal.Quotient.mk F (g₀ x.1 * f)) = 0
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))
    refine Nat.card_eq_of_bijective (fun x => ⟨⟨_, hmem1 x⟩, hmem2 x⟩)
      ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have e : Ideal.Quotient.mk F (g₀ x.1 * f) = Ideal.Quotient.mk F (g₀ y.1 * f) :=
        congrArg (fun z : ψ.ker => (z.1.1 : MRing ι ⧸ F)) hxy
      rw [Ideal.Quotient.eq, ← sub_mul, ← hq] at e
      apply Subtype.ext
      rw [← hg₀ x.1, ← hg₀ y.1]
      exact Ideal.Quotient.eq.2 e
    · obtain ⟨⟨y, hy⟩, hz⟩ := z
      obtain ⟨h, hh, rfl⟩ := mem_multidegree_piece_iff.1 hy
      rw [AddMonoidHom.mem_ker, hψ] at hz
      change Ideal.Quotient.factor hle (Ideal.Quotient.mk F h) = 0 at hz
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_sup] at hz
      obtain ⟨u, hu, v, hv, huv⟩ := hz
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hv
      have hx : Ideal.Quotient.mk q (i2comp (a - c) g) ∈ mPiece q (a - c) :=
        mem_multidegree_piece_iff.2 ⟨_, isMultiHomog_i2comp _ _, rfl⟩
      refine ⟨⟨_, hx⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      show Ideal.Quotient.mk F (g₀ (Ideal.Quotient.mk q (i2comp (a - c) g)) * f) =
        Ideal.Quotient.mk F h
      rw [quotient_mk_mul_congr_colon hq (hg₀ _)]
      have e : h = i2comp a u + i2comp (a - c) g * f := by
        rw [← i2comp_self hh, ← huv, i2comp_add, i2comp_mul_right hf, if_pos hca]
      rw [e, Ideal.Quotient.eq]
      have e2 : i2comp (a - c) g * f - (i2comp a u + i2comp (a - c) g * f) = -i2comp a u := by ring
      rw [e2]
      exact neg_mem (i2comp_mem hF a hu)
  rw [h1, h2, ← h3, mul_comm]

theorem card_piece_top_ideal (a : K → ℕ) : Nat.card (mPiece (⊤ : Ideal (MRing ι)) a) = 1 := by
  haveI : Subsingleton (MRing ι ⧸ (⊤ : Ideal (MRing ι))) := Ideal.Quotient.subsingleton_iff.2 rfl
  exact Nat.card_of_subsingleton (0 : mPiece (⊤ : Ideal (MRing ι)) a)

theorem card_piece_of_filtration : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι)
    (c : Fin N → K → ℕ) (q : Fin N → Ideal (MRing ι)), IsMultiHomogIdeal (F 0) →
    F (Fin.last N) = ⊤ →
    (∀ j, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    ∀ a : K → ℕ, (∀ j, c j ≤ a) →
      Nat.card (mPiece (F 0) a) = ∏ j, Nat.card (mPiece (q j) (a - c j))
  | 0, F, f, c, q, _, hl, _, a, _ => by
    have : F 0 = ⊤ := hl
    rw [Finset.univ_eq_empty, Finset.prod_empty, this, card_piece_top_ideal]
  | N + 1, F, f, c, q, h0, hl, hs, a, ha => by
    obtain ⟨hf0, hF1, hq0⟩ := hs 0
    rw [Fin.castSucc_zero] at hF1 hq0
    have e1 := card_piece_colon_exact h0 hf0 hq0 (ha 0)
    rw [← hF1] at e1
    have h0' : IsMultiHomogIdeal (F (Fin.succ 0)) := by
      rw [hF1]
      exact isMultiHomogIdeal_sup_span h0 hf0
    have ih := card_piece_of_filtration N (fun i => F i.succ) (fun j => f j.succ) (fun j => c j.succ)
      (fun j => q j.succ) h0' (by simp only [Fin.succ_last]; exact hl)
      (fun j => by
        obtain ⟨x1, x2, x3⟩ := hs j.succ
        refine ⟨x1, ?_, ?_⟩
        · simp only [Fin.succ_castSucc] at x2 ⊢
          exact x2
        · simpa only [Fin.succ_castSucc] using x3) a (fun j => ha j.succ)
    rw [Fin.prod_univ_succ, e1]
    congr 1

theorem card_piece_irrelevant_ideal {q : Ideal (MRing ι)} {k : K} (hk : ∀ i, (X ⟨k, i⟩ : MRing ι) ∈ q)
    {a : K → ℕ} (ha : 1 ≤ a k) : Nat.card (mPiece q a) = 1 := by
  have key : ∀ y ∈ mPiece q a, y = 0 := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := mem_multidegree_piece_iff.1 hy
    rw [Ideal.Quotient.eq_zero_iff_mem, h.as_sum]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hmk : i2bdeg m k = a k :=
      congrFun ((isMultiHomog_iff_coeff h a).1 hh m (mem_support_iff.1 hm)) k
    have : ∃ i, m ⟨k, i⟩ ≠ 0 := by
      by_contra hne
      push_neg at hne
      have h0 : i2bdeg m k = 0 := show ∑ i, m ⟨k, i⟩ = 0 from Finset.sum_eq_zero fun i _ => hne i
      rw [h0] at hmk
      rw [← hmk] at ha
      exact absurd ha (by norm_num)
    obtain ⟨i, hi⟩ := this
    have hle : Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1 ≤ m :=
      Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
    have e : monomial m (coeff m h) =
        X ⟨k, i⟩ * monomial (m - Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1) (coeff m h) := by
      rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le hle]
    rw [e]
    exact Ideal.mul_mem_right _ _ (hk i)
  haveI : Subsingleton (mPiece q a) :=
    ⟨fun x y => Subtype.ext ((key _ x.2).trans (key _ y.2).symm)⟩
  exact Nat.card_of_subsingleton (0 : mPiece q a)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
