import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreservingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankOneSphericalIntegrandDiagonalTorusFac

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

namespace SymmetricIndexCases

theorem wexp_lOf {n : ℕ} (x : Fin n → ℤ) (i : Fin n) : wexp n (lOf x) i = x i - x i.rev := by
  have hc : ∀ j k : Fin n, j.val = k.val → x j = x k := fun j k h => congrArg x (Fin.ext h)
  have hi := i.isLt
  unfold wexp lOf
  split_ifs with h h'
  · congr 1 <;> apply hc <;> simp [Fin.val_rev] <;> omega
  · rw [neg_sub]
    congr 1 <;> apply hc <;> simp [Fin.val_rev] <;> omega
  · rw [hc i.rev i (by simp [Fin.val_rev]; omega), sub_self]

theorem wexp_rev {n : ℕ} (x : Fin n → ℤ) (i : Fin n) : wexp n (lOf x) i.rev = -wexp n (lOf x) i := by
  rw [wexp_lOf, wexp_lOf, Fin.rev_rev]
  ring

theorem wexp_strictAnti {n : ℕ} (x : Fin n → ℤ) (hx : StrictAnti x) : StrictAnti (wexp n (lOf x)) := by
  intro i j hij
  rw [wexp_lOf, wexp_lOf]
  have h1 := hx hij
  have h2 : x i.rev < x j.rev := hx (Fin.rev_lt_rev.mpr hij)
  linarith

theorem emb_rev {n m : ℕ} (S : Finset (Fin n)) (hS : ∀ i, i ∈ S → i.rev ∈ S) (h : S.card = m) (j : Fin m) :
    S.orderEmbOfFin h j.rev = (S.orderEmbOfFin h j).rev := by
  have key := Finset.orderEmbOfFin_unique h (f := fun j => (S.orderEmbOfFin h j.rev).rev)
    (fun j => hS _ (Finset.orderEmbOfFin_mem S h _))
    (fun j k hjk => Fin.rev_lt_rev.mpr ((S.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.mpr hjk)))
  have := congrFun key j.rev
  simp only [Fin.rev_rev] at this
  exact this.symm

theorem nv_restr {n m : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) (hS : ∀ i, i ∈ S → i.rev ∈ S) (h : S.card = m)
    (j : Fin m) : nv (restr x S h) j = wexp n (lOf x) (S.orderEmbOfFin h j) := by
  simp only [nv, restr]
  rw [wexp_lOf, emb_rev S hS h j]

theorem prod_emb {n m : ℕ} {M : Type*} [CommMonoid M] (S : Finset (Fin n)) (h : S.card = m) (f : Fin n → M) :
    ∏ j : Fin m, f (S.orderEmbOfFin h j) = ∏ i ∈ S, f i := by
  rw [← Finset.prod_coe_sort S f]
  exact Fintype.prod_equiv (S.orderIsoOfFin h).toEquiv _ _ (fun j => by simp [Finset.coe_orderIsoOfFin_apply])

theorem symIdx_rev (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) (i : Fin n)
    (hi : i ∈ symIdx n mid s) : i.rev ∈ symIdx n mid s := by
  have hlt := i.isLt
  simp only [symIdx, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hi ⊢
  rcases hi with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm, ho, he⟩
  · right; left
    refine ⟨by omega, ?_⟩
    convert hs using 2
    omega
  · left
    refine ⟨by omega, ?_⟩
    convert hs using 2
    omega
  · right; right
    exact ⟨hm, ho, by omega⟩

theorem symIdx_congr (n : ℕ) (mid mid' : Prop) [Decidable mid] [Decidable mid'] (hm : mid ↔ mid')
    (s : Finset (Fin (n / 2))) : symIdx n mid s = symIdx n mid' s := by
  ext i
  simp only [symIdx, Finset.mem_filter, Finset.mem_univ, true_and, hm]

def emb1 (n : ℕ) : Fin (n / 2) ↪ Fin n :=
  ⟨fun k => ⟨k.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

def emb2 (n : ℕ) : Fin (n / 2) ↪ Fin n :=
  ⟨fun k => ⟨n - 1 - k.val, by omega⟩, fun a b h => Fin.ext (by
    have h1 := congrArg Fin.val h
    have := a.isLt
    have := b.isLt
    simp only at h1
    omega)⟩

@[simp] theorem block_embedding_first_val (n : ℕ) (k : Fin (n / 2)) : (emb1 n k).val = k.val := rfl

@[simp] theorem block_embedding_second_val (n : ℕ) (k : Fin (n / 2)) : (emb2 n k).val = n - 1 - k.val := rfl

theorem card_symIdx (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) :
    (symIdx n mid s).card = 2 * s.card + (if mid ∧ n % 2 = 1 then 1 else 0) := by
  let ι₁ := emb1 n
  let ι₂ := emb2 n
  have hsplit : symIdx n mid s = (s.map ι₁ ∪ s.map ι₂) ∪
      Finset.univ.filter (fun i : Fin n => mid ∧ n % 2 = 1 ∧ i.val = n / 2) := by
    ext i
    have hlt := i.isLt
    simp only [symIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map]
    constructor
    · rintro (⟨h, hs⟩ | ⟨h, hs⟩ | hm)
      · exact Or.inl (Or.inl ⟨_, hs, Fin.ext rfl⟩)
      · refine Or.inl (Or.inr ⟨_, hs, Fin.ext ?_⟩)
        simp only [ι₂, block_embedding_second_val]
        omega
      · exact Or.inr hm
    · rintro ((⟨k, hs, rfl⟩ | ⟨k, hs, rfl⟩) | hm)
      · exact Or.inl ⟨k.isLt, hs⟩
      · have hk := k.isLt
        refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · simp only [ι₂, block_embedding_second_val]
          omega
        · convert hs using 1
          ext
          simp only [ι₂, block_embedding_second_val]
          omega
      · exact Or.inr (Or.inr hm)
  have hd1 : Disjoint (s.map ι₁) (s.map ι₂) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_map] at h1 h2
    obtain ⟨k, -, rfl⟩ := h1
    obtain ⟨k', -, hk'⟩ := h2
    have := k.isLt
    have := k'.isLt
    have h3 := congrArg Fin.val hk'
    simp only [ι₁, ι₂, block_embedding_first_val, block_embedding_second_val] at h3
    omega
  have hd2 : Disjoint (s.map ι₁ ∪ s.map ι₂)
      (Finset.univ.filter (fun i : Fin n => mid ∧ n % 2 = 1 ∧ i.val = n / 2)) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
    simp only [Finset.mem_union, Finset.mem_map] at h1
    rcases h1 with ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩
    · have := k.isLt
      simp only [ι₁, block_embedding_first_val] at h2
      omega
    · have := k.isLt
      simp only [ι₂, block_embedding_second_val] at h2
      omega
  have hM : (Finset.univ.filter (fun i : Fin n => mid ∧ n % 2 = 1 ∧ i.val = n / 2)).card =
      if mid ∧ n % 2 = 1 then 1 else 0 := by
    split_ifs with hc
    · rw [Finset.card_eq_one]
      refine ⟨⟨n / 2, by omega⟩, ?_⟩
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
      exact ⟨fun h => h.2.2, fun h => ⟨hc.1, hc.2, h⟩⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ h
      exact hc ⟨h.1, h.2.1⟩
  rw [hsplit, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, Finset.card_map,
    Finset.card_map, hM]
  ring

theorem symIdx_union (n a : ℕ) (ha : a ≤ n) (s : Finset (Fin (n / 2))) (hp : a % 2 + (n - a) % 2 = n % 2) :
    symIdx n (a % 2 = 1) s ∪ symIdx n ((n - a) % 2 = 1) sᶜ = Finset.univ := by
  ext i
  have hlt := i.isLt
  simp only [symIdx, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, iff_true]
  by_cases h1 : i.val < n / 2
  · by_cases hs : (⟨i.val, h1⟩ : Fin (n / 2)) ∈ s
    · exact Or.inl (Or.inl ⟨h1, hs⟩)
    · exact Or.inr (Or.inl ⟨h1, hs⟩)
  by_cases h2 : n - 1 - i.val < n / 2
  · by_cases hs : (⟨n - 1 - i.val, h2⟩ : Fin (n / 2)) ∈ s
    · exact Or.inl (Or.inr (Or.inl ⟨h2, hs⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h2, hs⟩))
  have ho : n % 2 = 1 := by omega
  have hm : i.val = n / 2 := by omega
  by_cases hp1 : a % 2 = 1
  · exact Or.inl (Or.inr (Or.inr ⟨hp1, ho, hm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, ho, hm⟩))

def half {n : ℕ} (T : Finset (Fin n)) : Finset (Fin (n / 2)) :=
  Finset.univ.filter fun k => (⟨k.val, by omega⟩ : Fin n) ∈ T

theorem half_compl {n : ℕ} (T : Finset (Fin n)) : half Tᶜ = (half T)ᶜ := by
  ext k
  simp [half]

theorem eq_symIdx_half {n : ℕ} (T : Finset (Fin n)) (hT : ∀ i, i ∈ T → i.rev ∈ T) :
    T = symIdx n (∃ j ∈ T, j.val = n / 2 ∧ n % 2 = 1) (half T) := by
  ext i
  have hlt := i.isLt
  simp only [symIdx, half, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    by_cases h1 : i.val < n / 2
    · exact Or.inl ⟨h1, by simpa using hi⟩
    by_cases h2 : n - 1 - i.val < n / 2
    · refine Or.inr (Or.inl ⟨h2, ?_⟩)
      convert hT i hi using 1
      ext
      simp [Fin.val_rev]
      omega
    · exact Or.inr (Or.inr ⟨⟨i, hi, by omega, by omega⟩, by omega, by omega⟩)
  · rintro (⟨h, hs⟩ | ⟨h, hs⟩ | ⟨⟨j, hj, hj1, -⟩, -, he⟩)
    · simpa using hs
    · have := hT _ hs
      convert this using 1
      ext
      simp [Fin.val_rev]
      omega
    · convert hj using 1
      ext
      omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hasVals_of_prod {w : Pl E} {n m : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) (hS : ∀ i, i ∈ S → i.rev ∈ S)
    (h : S.card = m) (u : Fin n → w.adicCompletion E) (hu : ∀ i ∈ S, u i ≠ 0 ∧ ordL (u i) = wexp n (lOf x) i)
    (Q : (w.adicCompletion E)[X]) (hQ : Q = ∏ i ∈ S, (X - C (u i))) : HasVals Q (nv (restr x S h)) :=
  ⟨fun j => u (S.orderEmbOfFin h j), by rw [hQ, prod_emb S h (fun i => X - C (u i))],
    fun j => by rw [nv_restr x S hS h j]; exact hu _ (Finset.orderEmbOfFin_mem S h j)⟩

theorem prod_of_hasVals {w : Pl E} {n m : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) (hS : ∀ i, i ∈ S → i.rev ∈ S)
    (h : S.card = m) (Q : (w.adicCompletion E)[X]) (hv : HasVals Q (nv (restr x S h))) :
    ∃ u : Fin n → w.adicCompletion E, Q = ∏ i ∈ S, (X - C (u i)) ∧
      ∀ i ∈ S, u i ≠ 0 ∧ ordL (u i) = wexp n (lOf x) i := by
  obtain ⟨v, hQ, hv⟩ := hv
  refine ⟨fun i => if hi : i ∈ S then v ((S.orderIsoOfFin h).symm ⟨i, hi⟩) else 1, ?_, ?_⟩
  · rw [hQ, ← prod_emb S h]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hm := Finset.orderEmbOfFin_mem S h j
    have hk : (S.orderIsoOfFin h).symm ⟨S.orderEmbOfFin h j, hm⟩ = j :=
      (S.orderIsoOfFin h).symm_apply_eq.mpr (Subtype.ext (Finset.coe_orderIsoOfFin_apply S h j).symm)
    simp only [dif_pos hm, hk]
  · intro i hi
    simp only [dif_pos hi]
    have hk : S.orderEmbOfFin h ((S.orderIsoOfFin h).symm ⟨i, hi⟩) = i := by
      rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    refine ⟨(hv _).1, ?_⟩
    rw [(hv _).2, nv_restr x S hS h, hk]

theorem csr_root {w : Pl E} (hw : ¬ IsSplitAt w) {Q : (w.adicCompletion E)[X]} (hm : Q.Monic) (hc : IsCsr w Q)
    (h0 : Q.coeff 0 ≠ 0) {r : w.adicCompletion E} (hr : r ∈ Q.roots) : (cj w r)⁻¹ ∈ Q.roots := by
  have hc' : C (cj w (Q.coeff 0)) * Q = (Q.map (cj w)).reverse := hc.resolve_left hw
  have hQ0 : Q ≠ 0 := hm.ne_zero
  rw [mem_roots hQ0] at hr ⊢
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact h0 (by rw [coeff_zero_eq_eval_zero]; exact hr)
  have hcr : cj w r ≠ 0 := (_root_.map_ne_zero _).mpr hr0
  let _ : Invertible (cj w r) := invertibleOfNonzero hcr
  have h1 : eval₂ (RingHom.id _) (⅟(cj w r)) (Q.map (cj w)).reverse = 0 := by
    rw [eval₂_reverse_eq_zero_iff, eval₂_map, RingHom.id_comp, eval₂_at_apply, hr.eq_zero, map_zero]
  have h2 : eval (cj w r)⁻¹ (C (cj w (Q.coeff 0)) * Q) = 0 := by
    rw [hc', ← invOf_eq_inv]
    exact h1
  rw [eval_mul, eval_C] at h2
  exact (mul_eq_zero.mp h2).resolve_left ((_root_.map_ne_zero _).mpr h0)

end SymmetricIndexCases

open SymmetricIndexCases

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem combine_caseA_pf (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (x : Fin n → ℤ) (hx : StrictAnti x)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) (s : Finset (Fin (n / 2))) (hA : CaseA w n a x Q₁ Q₂ s) :
    HasVals (Q₁ * Q₂) (wexp n (lOf x)) := by
  obtain ⟨_, _, hpar, h₁, h₂, hv₁, hv₂⟩ := hA
  obtain ⟨u₁, hQ₁, hu₁⟩ := prod_of_hasVals x _ (symIdx_rev n _ s) h₁ Q₁ hv₁
  obtain ⟨u₂, hQ₂, hu₂⟩ := prod_of_hasVals x _ (symIdx_rev n _ sᶜ) h₂ Q₂ hv₂
  have hU := symIdx_union n a ha s hpar
  set S₁ := symIdx n (a % 2 = 1) s with hS₁
  set S₂ := symIdx n ((n - a) % 2 = 1) sᶜ with hS₂
  have hD : Disjoint S₁ S₂ := by
    have hc := Finset.card_union_add_card_inter S₁ S₂
    rw [hU, h₁, h₂, Finset.card_univ, Fintype.card_fin] at hc
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
    omega
  refine ⟨fun i => if i ∈ S₁ then u₁ i else u₂ i, ?_, ?_⟩
  · symm
    calc (∏ i, (X - C (if i ∈ S₁ then u₁ i else u₂ i)))
        = ∏ i ∈ S₁ ∪ S₂, (X - C (if i ∈ S₁ then u₁ i else u₂ i)) := by rw [hU]
      _ = (∏ i ∈ S₁, (X - C (if i ∈ S₁ then u₁ i else u₂ i))) *
          ∏ i ∈ S₂, (X - C (if i ∈ S₁ then u₁ i else u₂ i)) := Finset.prod_union hD
      _ = Q₁ * Q₂ := by
        rw [hQ₁, hQ₂]
        congr 1
        · exact Finset.prod_congr rfl fun i hi => by simp only [if_pos hi]
        · exact Finset.prod_congr rfl fun i hi => by simp only [if_neg (Finset.disjoint_right.mp hD hi)]
  · intro i
    by_cases hi : i ∈ S₁
    · simp only [if_pos hi]
      exact hu₁ i hi
    · have hi2 : i ∈ S₂ := by
        have := Finset.mem_univ i
        rw [← hU, Finset.mem_union] at this
        exact this.resolve_left hi
      simp only [if_neg hi]
      exact hu₂ i hi2

theorem split_caseA_pf (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (x : Fin n → ℤ) (hx : StrictAnti x)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic) (hd₁ : Q₁.natDegree = a)
    (hd₂ : Q₂.natDegree = n - a) (hc₁ : IsCsr w Q₁) (hc₂ : IsCsr w Q₂) (hv : HasVals (Q₁ * Q₂) (wexp n (lOf x))) :
    ∃ s, CaseA w n a x Q₁ Q₂ s := by
  obtain ⟨u, hP, hu⟩ := hv
  have hanti := wexp_strictAnti x hx
  have hinj : Function.Injective u := fun i j h => hanti.injective (by rw [← (hu i).2, ← (hu j).2, h])
  have hne : Q₁ * Q₂ ≠ 0 := (hm₁.mul hm₂).ne_zero
  have hroots : (Q₁ * Q₂).roots = Finset.univ.val.map u := by
    have e : (Finset.univ.val.map fun i => X - C (u i)) = (Finset.univ.val.map u).map (fun r => X - C r) := by
      rw [Multiset.map_map]
      rfl
    rw [hP, Finset.prod_eq_multiset_prod, e, roots_multiset_prod_X_sub_C]
  have hr : Q₁.roots + Q₂.roots = Finset.univ.val.map u := by rw [← roots_mul hne, hroots]
  have hnd : (Q₁.roots + Q₂.roots).Nodup := by
    rw [hr]
    exact Multiset.Nodup.map hinj Finset.univ.nodup
  have hcard : Multiset.card Q₁.roots + Multiset.card Q₂.roots = n := by
    rw [← Multiset.card_add, hr, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  have hc1 : Multiset.card Q₁.roots = a := by
    have := card_roots' Q₁
    have := card_roots' Q₂
    omega
  have hc2 : Multiset.card Q₂.roots = n - a := by omega
  have hQ₁ := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm₁ (by rw [hc1, hd₁])
  have hQ₂ := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm₂ (by rw [hc2, hd₂])
  set T : Finset (Fin n) := Finset.univ.filter (fun i => u i ∈ Q₁.roots) with hT
  have hmemT : ∀ i, i ∈ T ↔ u i ∈ Q₁.roots := fun i => by simp [hT]
  have hcount : ∀ r, ¬ (r ∈ Q₁.roots ∧ r ∈ Q₂.roots) := by
    rintro r ⟨h1, h2⟩
    have h3 := Multiset.nodup_iff_count_le_one.mp hnd r
    rw [Multiset.count_add] at h3
    have := Multiset.count_pos.mpr h1
    have := Multiset.count_pos.mpr h2
    omega
  have hmemU : ∀ i, u i ∈ Q₁.roots ∨ u i ∈ Q₂.roots := fun i => by
    rw [← Multiset.mem_add, hr]
    exact Multiset.mem_map_of_mem u (Finset.mem_univ_val i)
  have hR₁ : Q₁.roots = T.val.map u := by
    rw [Multiset.Nodup.ext (Multiset.nodup_of_le (Multiset.le_add_right _ _) hnd) (Multiset.Nodup.map hinj T.nodup)]
    intro r
    constructor
    · intro h1
      have : r ∈ Finset.univ.val.map u := hr ▸ Multiset.mem_add.mpr (Or.inl h1)
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp this
      exact Multiset.mem_map_of_mem u ((hmemT i).mpr h1)
    · intro h
      obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp h
      exact (hmemT i).mp hi
  have hR₂ : Q₂.roots = Tᶜ.val.map u := by
    rw [Multiset.Nodup.ext (Multiset.nodup_of_le (Multiset.le_add_left _ _) hnd) (Multiset.Nodup.map hinj Tᶜ.nodup)]
    intro r
    constructor
    · intro h2
      have : r ∈ Finset.univ.val.map u := hr ▸ Multiset.mem_add.mpr (Or.inr h2)
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp this
      refine Multiset.mem_map_of_mem u (Finset.mem_compl.mpr fun hi => hcount (u i) ⟨(hmemT i).mp hi, h2⟩)
    · intro h
      obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp h
      have hi' : i ∉ T := Finset.mem_compl.mp hi
      exact (hmemU i).resolve_left fun h1 => hi' ((hmemT i).mpr h1)
  have hTcard : T.card = a := by rw [← hc1, hR₁, Multiset.card_map, Finset.card_val]
  have hTccard : Tᶜ.card = n - a := by rw [← hc2, hR₂, Multiset.card_map, Finset.card_val]
  have hQ₁T : Q₁ = ∏ i ∈ T, (X - C (u i)) := by
    rw [Finset.prod_eq_multiset_prod]
    conv_lhs => rw [← hQ₁]
    rw [hR₁, Multiset.map_map]
    rfl
  have hQ₂T : Q₂ = ∏ i ∈ Tᶜ, (X - C (u i)) := by
    rw [Finset.prod_eq_multiset_prod]
    conv_lhs => rw [← hQ₂]
    rw [hR₂, Multiset.map_map]
    rfl
  have h0₁ : Q₁.coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero]
    intro h
    have h0 : (0 : w.adicCompletion E) ∈ Q₁.roots := (mem_roots hm₁.ne_zero).mpr h
    rw [hR₁] at h0
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp h0
    exact (hu i).1 hi
  have hsym : ∀ i, i ∈ T → i.rev ∈ T := by
    intro i hi
    have hy := csr_root hw hm₁ hc₁ h0₁ ((hmemT i).mp hi)
    rw [hR₁] at hy
    obtain ⟨k, hk, hku⟩ := Multiset.mem_map.mp hy
    have hkr : k = i.rev := by
      apply hanti.injective
      rw [← (hu k).2, hku, GlobalTheory.WeylCell.U21TorusFactor.ordL_inv,
        GlobalTheory.WeylCell.U21TorusFactor.ordL_map (GlobalTheory.T.localConjugation_involutive_valuation_preserving E w).2, (hu i).2, wexp_rev]
    rw [← hkr]
    exact hk
  have hsymc : ∀ i, i ∈ Tᶜ → i.rev ∈ Tᶜ := fun i hi => by
    rw [Finset.mem_compl] at hi ⊢
    exact fun h => hi (by simpa using hsym _ h)
  have eT := eq_symIdx_half T hsym
  have eTc := eq_symIdx_half Tᶜ hsymc
  have cT := card_symIdx n (∃ j ∈ T, j.val = n / 2 ∧ n % 2 = 1) (half T)
  have cTc := card_symIdx n (∃ j ∈ Tᶜ, j.val = n / 2 ∧ n % 2 = 1) (half Tᶜ)
  rw [← eT, hTcard] at cT
  rw [← eTc, hTccard, half_compl] at cTc
  have hcs : (half T).card + (half T)ᶜ.card = n / 2 := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ (half T)
    rw [Fintype.card_fin] at this
    omega
  have hex : ¬ ((∃ j ∈ T, j.val = n / 2 ∧ n % 2 = 1) ∧ (∃ j ∈ Tᶜ, j.val = n / 2 ∧ n % 2 = 1)) := by
    rintro ⟨⟨j, hj, hj1, -⟩, ⟨j', hj', hj1', -⟩⟩
    have : j = j' := Fin.ext (hj1.trans hj1'.symm)
    exact (Finset.mem_compl.mp hj') (this ▸ hj)
  have hcases : (a % 2 = 1 ↔ ∃ j ∈ T, j.val = n / 2 ∧ n % 2 = 1) ∧
      ((n - a) % 2 = 1 ↔ ∃ j ∈ Tᶜ, j.val = n / 2 ∧ n % 2 = 1) ∧ (half T).card = a / 2 ∧
      (half T)ᶜ.card = (n - a) / 2 ∧ a % 2 + (n - a) % 2 = n % 2 := by
    by_cases hp1 : ∃ j ∈ T, j.val = n / 2 ∧ n % 2 = 1 <;> by_cases hp2 : ∃ j ∈ Tᶜ, j.val = n / 2 ∧ n % 2 = 1
    · exact absurd ⟨hp1, hp2⟩ hex
    · have ho : n % 2 = 1 := by obtain ⟨_, _, _, ho⟩ := hp1; exact ho
      rw [if_pos ⟨hp1, ho⟩] at cT
      rw [if_neg fun h => hp2 h.1] at cTc
      exact ⟨iff_of_true (by omega) hp1, iff_of_false (by omega) hp2, by omega, by omega, by omega⟩
    · have ho : n % 2 = 1 := by obtain ⟨_, _, _, ho⟩ := hp2; exact ho
      rw [if_neg fun h => hp1 h.1] at cT
      rw [if_pos ⟨hp2, ho⟩] at cTc
      exact ⟨iff_of_false (by omega) hp1, iff_of_true (by omega) hp2, by omega, by omega, by omega⟩
    · rw [if_neg fun h => hp1 h.1] at cT
      rw [if_neg fun h => hp2 h.1] at cTc
      exact ⟨iff_of_false (by omega) hp1, iff_of_false (by omega) hp2, by omega, by omega, by omega⟩
  obtain ⟨hm1, hm2, hsc1, hsc2, hpar⟩ := hcases
  have hS₁ : symIdx n (a % 2 = 1) (half T) = T := by
    rw [symIdx_congr n _ _ hm1]
    exact eT.symm
  have hS₂ : symIdx n ((n - a) % 2 = 1) (half T)ᶜ = Tᶜ := by
    rw [← half_compl, symIdx_congr n _ _ hm2]
    exact eTc.symm
  refine ⟨half T, hsc1, hsc2, hpar, by rw [hS₁]; exact hTcard, by rw [hS₂]; exact hTccard, ?_, ?_⟩
  · exact hasVals_of_prod x _ (symIdx_rev n _ _) _ u (fun i _ => hu i) Q₁ (by rw [hS₁]; exact hQ₁T)
  · exact hasVals_of_prod x _ (symIdx_rev n _ _) _ u (fun i _ => hu i) Q₂ (by rw [hS₂]; exact hQ₂T)

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
