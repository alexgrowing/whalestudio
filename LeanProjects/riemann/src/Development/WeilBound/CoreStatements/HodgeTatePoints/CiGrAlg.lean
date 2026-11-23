import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuationsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundlesStatement

open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ci

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {n : ℕ}

theorem step_basis (β : Module.Basis (Fin n) K V) {s : ℕ} (hs : s ≤ n) {W : Submodule K V}
    (hW : W = Submodule.span K (β '' {k | (k : ℕ) < s})) :
    ∃ γ : Module.Basis (Fin s) K W, (∀ k, (γ k : V) = β (Fin.castLE hs k)) ∧
      (∀ (x : W) k, β.repr x (Fin.castLE hs k) = γ.repr x k) ∧
      ∀ (x : W) (l : Fin n), s ≤ l → β.repr x l = 0 := by
  subst hW
  have hmem : ∀ k : Fin s, β (Fin.castLE hs k) ∈ Submodule.span K (β '' {k | (k : ℕ) < s}) :=
    fun k => Submodule.subset_span ⟨Fin.castLE hs k, by simp, rfl⟩
  let f : Fin s → Submodule.span K (β '' {k | (k : ℕ) < s}) := fun k => ⟨β (Fin.castLE hs k), hmem k⟩
  have hli : LinearIndependent K f := by
    apply LinearIndependent.of_comp (Submodule.span K (β '' {k | (k : ℕ) < s})).subtype
    exact β.linearIndependent.comp _ (Fin.castLE_injective hs)
  have hsp : ⊤ ≤ Submodule.span K (Set.range f) := by
    rw [← Submodule.span_span_coe_preimage (R := K) (s := β '' {k | (k : ℕ) < s})]
    apply Submodule.span_mono
    intro y hy
    obtain ⟨k, hk, hky⟩ := hy
    refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
    show β (Fin.castLE hs ⟨k, hk⟩) = y
    exact hky
  let γ := Module.Basis.mk hli hsp
  have hγ : ∀ k, (γ k : V) = β (Fin.castLE hs k) := fun k => by simp [γ, f]
  have key : ∀ (x : Submodule.span K (β '' {k | (k : ℕ) < s})) (l : Fin n),
      β.repr x l = ∑ k, γ.repr x k * (if Fin.castLE hs k = l then 1 else 0) := by
    intro x l
    conv_lhs => rw [← γ.sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, hγ, map_sum, map_smul, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  refine ⟨γ, hγ, fun x k => ?_, fun x l hl => ?_⟩
  · rw [key, Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [(Fin.castLE_injective hs).ne hj]
    · simp
  · rw [key]
    apply Finset.sum_eq_zero
    intro k _
    have : Fin.castLE hs k ≠ l := by
      intro h
      rw [← h] at hl
      simp at hl
      omega
    simp [this]

private theorem isLatOf_sub_of_basis_castLE (C : ACurve K) {Λ : C.I → AddSubgroup V} (i : C.I)
    (e : Module.Basis (Fin n) K V) {s : ℕ} (hs : s ≤ n) {W : Submodule K V}
    (ε : Module.Basis (Fin s) K W)
    (h2 : ∀ (x : W) k, e.repr x (Fin.castLE hs k) = ε.repr x k)
    (h3 : ∀ (x : W) (l : Fin n), s ≤ l → e.repr x l = 0)
    (he : IsLatOf C i e (Λ i)) : IsLatOf C i ε (sub C Λ W i) := by
  unfold IsLatOf at he ⊢
  intro x
  have hx : x ∈ sub C Λ W i ↔ (x : V) ∈ Λ i := Iff.rfl
  rw [hx, he]
  constructor
  · intro h k
    rw [← h2]
    exact h _
  · intro h q
    by_cases hq : (q : ℕ) < s
    · have hq' : q = Fin.castLE hs ⟨q, hq⟩ := rfl
      rw [hq', h2]
      exact h _
    · rw [h3 x q (by omega)]
      simp

private theorem v_repr_le_one_of_basis_change (C : ACurve K) (i : C.I) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : Module.Basis ι K V) (e' : Module.Basis ι' K V) (hee : ∀ k l, C.v i (e'.repr (e k) l) ≤ 1)
    (x : V) (hx : ∀ k, C.v i (e.repr x k) ≤ 1) (l : ι') : C.v i (e'.repr x l) ≤ 1 := by
  have hsum : e'.repr x l = ∑ k, e.repr x k * e'.repr (e k) l := by
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
  rw [hsum]
  apply Valuation.map_sum_le
  intro k _
  rw [map_mul]
  exact mul_le_one' (hx k) (hee k l)

private theorem finite_setOf_not_isLatOf (C : ACurve K) {Λ : C.I → AddSubgroup V} (hΛ : IsBun C Λ)
    (β : Module.Basis (Fin n) K V) : {i | ¬ IsLatOf C i β (Λ i)}.Finite := by
  obtain ⟨-, b0, hb0⟩ := hΛ
  have hfin : ∀ e : K, {i | 1 < C.v i e}.Finite := by
    intro e
    by_cases he : e = 0
    · simp [he]
    · exact (C.fin e he).subset (fun i hi => ne_of_gt hi)
  have hS : ({i | ¬IsLatOf C i b0 (Λ i)} ∪ (⋃ k, ⋃ l, {i | 1 < C.v i (β.repr (b0 k) l)}) ∪
      (⋃ k, ⋃ l, {i | 1 < C.v i (b0.repr (β k) l)})).Finite :=
    (hb0.union (Set.finite_iUnion fun k => Set.finite_iUnion fun l => hfin _)).union
      (Set.finite_iUnion fun k => Set.finite_iUnion fun l => hfin _)
  apply hS.subset
  intro i hi
  by_contra hni
  apply hi
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_lt,
    not_not] at hni
  obtain ⟨⟨h0, h1⟩, h2⟩ := hni
  unfold IsLatOf at h0 ⊢
  intro x
  rw [h0 x]
  exact ⟨fun hx l => v_repr_le_one_of_basis_change C i b0 β h1 x hx l, fun hx l => v_repr_le_one_of_basis_change C i β b0 h2 x hx l⟩

private theorem isLatOf_reindex' (C : ACurve K) (i : C.I) {U : Type} [AddCommGroup U] [Module K U]
    {m r : ℕ} (d : Module.Basis (Fin m) K U) (e : Fin m ≃ Fin r) (L : AddSubgroup U)
    (h : IsLatOf C i d L) : IsLatOf C i (d.reindex e) L := by
  unfold IsLatOf at h ⊢
  intro x
  rw [h x]
  simp only [Module.Basis.repr_reindex_apply]
  exact ⟨fun hx q => hx _, fun hx k => by simpa using hx (e k)⟩

theorem subDeg_step [FiniteDimensional K V] (C : ACurve K) {Λ : C.I → AddSubgroup V} (hΛ : IsBun C Λ)
    (β : Module.Basis (Fin n) K V) (b : C.I → Module.Basis (Fin n) K V) (hb : ∀ i, IsLatOf C i (b i) (Λ i))
    {s : ℕ} (hs : s ≤ n) (tri : ∀ i (k l : Fin n), (k : ℕ) < s → k < l → β.repr (b i k) l = 0) :
    (∀ i, ∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k) ≠ 0) ∧
      {i | C.v i (∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k)) ≠ 1}.Finite ∧
      subDeg C Λ (Submodule.span K (β '' {k | (k : ℕ) < s})) =
        ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k))) := by
  set W := Submodule.span K (β '' {k | (k : ℕ) < s}) with hWdef
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := step_basis β hs (W := W) rfl
  have hbi : ∀ i, W = Submodule.span K ((b i) '' {k | (k : ℕ) < s}) := by
    intro i
    obtain ⟨δ, -, -, -⟩ := step_basis (b i) hs (W := Submodule.span K ((b i) '' {k | (k : ℕ) < s})) rfl
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, hWdef, β.mem_span_image]
      intro l hl
      rw [Finset.mem_coe, Finsupp.mem_support_iff] at hl
      simp only [Set.mem_setOf_eq]
      by_contra hls
      exact hl (tri i k l hk (Fin.lt_iff_val_lt_val.mpr (by simp only [Set.mem_setOf_eq] at hk; omega)))
    · rw [Module.finrank_eq_card_basis δ, Module.finrank_eq_card_basis γ]
  choose δ hδ1 hδ2 hδ3 using fun i => step_basis (b i) hs (hbi i)
  have hlat : ∀ i, IsLatOf C i (δ i) (sub C Λ W i) :=
    fun i => isLatOf_sub_of_basis_castLE C i (b i) hs (δ i) (hδ2 i) (hδ3 i) (hb i)
  have hD : ∀ i, γ.det (δ i) = ∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k) := by
    intro i
    rw [Module.Basis.det_apply, Matrix.det_of_isUpperTriangular]
    · apply Finset.prod_congr rfl
      intro k _
      rw [Module.Basis.toMatrix_apply, ← hγ2, hδ1]
    · intro k l hlk
      rw [Module.Basis.toMatrix_apply, ← hγ2, hδ1]
      exact tri i _ _ (by simp) (Fin.lt_iff_val_lt_val.mpr (by simpa using hlk))
  have hne : ∀ i, ∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k) ≠ 0 := by
    intro i
    rw [← hD]
    exact (γ.isUnit_det (δ i)).ne_zero
  have hfinP : {i | C.v i (∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k)) ≠ 1}.Finite := by
    apply (finite_setOf_not_isLatOf C hΛ β).subset
    intro i hi hβ
    apply hi
    rw [← hD]
    exact Inhab.v_det C (isLatOf_sub_of_basis_castLE C i β hs γ hγ2 hγ3 hβ) (hlat i)
  refine ⟨hne, hfinP, ?_⟩
  have hr : Module.finrank K W = s := by rw [Module.finrank_eq_card_basis γ, Fintype.card_fin]
  set e : Fin s ≃ Fin (Module.finrank K W) := finCongr hr.symm
  have hdeg : subDeg C Λ W = ∑ᶠ i, (C.w i : ℤ) *
      WithZero.log (C.v i ((Module.finBasis K W).det ((δ i).reindex e))) :=
    Inhab.deg_eq C _ (fun i => isLatOf_reindex' C i (δ i) e _ (hlat i))
  rw [hdeg]
  set c := (Module.finBasis K W).det (γ.reindex e)
  have hc : c ≠ 0 := ((Module.finBasis K W).isUnit_det _).ne_zero
  have hsplit : ∀ i, (Module.finBasis K W).det ((δ i).reindex e) =
      c * ∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k) := by
    intro i
    rw [← hD, ← (Module.finBasis K W).det_mul_det (γ.reindex e) ((δ i).reindex e),
      Module.Basis.det_reindex]
    congr 2
    ext k
    simp
  simp_rw [hsplit]
  have hlog : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i (c * ∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k))) =
      (C.w i : ℤ) * WithZero.log (C.v i c) +
        (C.w i : ℤ) * WithZero.log (C.v i (∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k))) := by
    intro i
    rw [map_mul, WithZero.log_mul ((C.v i).ne_zero_iff.mpr hc) ((C.v i).ne_zero_iff.mpr (hne i)), mul_add]
  simp_rw [hlog]
  rw [finsum_add_distrib, C.prod c hc, zero_add]
  · apply (C.fin c hc).subset
    intro i hi h1
    apply hi
    simp [h1]
  · apply hfinP.subset
    intro i hi h1
    apply hi
    simp [h1]

theorem subDeg_succ [FiniteDimensional K V] (C : ACurve K) {Λ : C.I → AddSubgroup V} (hΛ : IsBun C Λ)
    (β : Module.Basis (Fin n) K V) (b : C.I → Module.Basis (Fin n) K V) (hb : ∀ i, IsLatOf C i (b i) (Λ i))
    (s : Fin n) (tri : ∀ i (k l : Fin n), k ≤ s → k < l → β.repr (b i k) l = 0) :
    (∀ i, β.repr (b i s) s ≠ 0) ∧ {i | C.v i (β.repr (b i s) s) ≠ 1}.Finite ∧
      subDeg C Λ (Submodule.span K (β '' {k | (k : ℕ) < s + 1})) -
          subDeg C Λ (Submodule.span K (β '' {k | (k : ℕ) < s})) =
        ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (β.repr (b i s) s)) := by
  have hs1 : (s : ℕ) + 1 ≤ n := s.isLt
  have hs0 : (s : ℕ) ≤ n := s.isLt.le
  obtain ⟨ne1, fin1, eq1⟩ := subDeg_step C hΛ β b hb hs1 (fun i k l hk hkl =>
    tri i k l (Fin.le_iff_val_le_val.mpr (by omega)) hkl)
  obtain ⟨ne0, fin0, eq0⟩ := subDeg_step C hΛ β b hb hs0 (fun i k l hk hkl =>
    tri i k l (Fin.le_iff_val_le_val.mpr (by omega)) hkl)
  have hprod : ∀ i, ∏ k : Fin ((s : ℕ) + 1), β.repr (b i (Fin.castLE hs1 k)) (Fin.castLE hs1 k) =
      (∏ k : Fin s, β.repr (b i (Fin.castLE hs0 k)) (Fin.castLE hs0 k)) * β.repr (b i s) s := by
    intro i
    rw [Fin.prod_univ_castSucc]
    have h1 : ∀ k : Fin s, Fin.castLE hs1 (Fin.castSucc k) = Fin.castLE hs0 k := fun k => Fin.ext (by simp)
    have h2 : Fin.castLE hs1 (Fin.last s) = s := Fin.ext (by simp)
    simp only [h1, h2]
  have hd : ∀ i, β.repr (b i s) s ≠ 0 := by
    intro i
    have := ne1 i
    rw [hprod] at this
    exact right_ne_zero_of_mul this
  have hdfin : {i | C.v i (β.repr (b i s) s) ≠ 1}.Finite := by
    apply (fin1.union fin0).subset
    intro i hi
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, hprod, map_mul] at hc
    obtain ⟨h1, h2⟩ := hc
    rw [h2, one_mul] at h1
    exact hi h1
  refine ⟨hd, hdfin, ?_⟩
  rw [eq1, eq0]
  have hlog : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i (∏ k : Fin ((s : ℕ) + 1),
      β.repr (b i (Fin.castLE hs1 k)) (Fin.castLE hs1 k))) =
      (C.w i : ℤ) * WithZero.log (C.v i (∏ k : Fin s, β.repr (b i (Fin.castLE hs0 k)) (Fin.castLE hs0 k))) +
        (C.w i : ℤ) * WithZero.log (C.v i (β.repr (b i s) s)) := by
    intro i
    rw [hprod, map_mul, WithZero.log_mul ((C.v i).ne_zero_iff.mpr (ne0 i)) ((C.v i).ne_zero_iff.mpr (hd i)),
      mul_add]
  simp_rw [hlog]
  rw [finsum_add_distrib, add_sub_cancel_left]
  · apply fin0.subset
    intro i hi h1
    apply hi
    simp [h1]
  · apply hdfin.subset
    intro i hi h1
    apply hi
    simp [h1]

end PositivityTheory.HtPt.Ci
