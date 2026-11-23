import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset

noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

namespace V1

section Ord

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_eq {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  simp [ordL, h0]

theorem ordL_eq_of_v {x : L} {k : ℤ}
    (h : Valued.v x = ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ordL x = -k := by
  have h0 : Valued.v x ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  have hu : WithZero.unzero h0 = Multiplicative.ofAdd k := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
  rw [ordL, dif_neg h0, hu, toAdd_ofAdd]

theorem ordL_one : ordL (1 : L) = 0 := by
  simpa using ordL_eq_of_v (x := (1 : L)) (k := 0) (by simp)

theorem ordL_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have := ordL_eq_of_v (x := x * y) (k := -(ordL x + ordL y))
    (by rw [map_mul, v_eq hx, v_eq hy, ← WithZero.coe_mul, ← ofAdd_add, neg_add])
  simpa using this

theorem ordL_neg (x : L) : ordL (-x) = ordL x := by
  unfold ordL
  simp only [Valuation.map_neg]

theorem ordL_prod {ι : Type*} (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, f i ≠ 0) :
    ordL (∏ i ∈ s, f i) = ∑ i ∈ s, ordL (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ordL_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ordL_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ordL_sub_of_lt {u v : L} (hu : u ≠ 0) (hv : v ≠ 0) (h : ordL u < ordL v) :
    ordL (u - v) = ordL u := by
  have hlt : Valued.v v < Valued.v u := by
    rw [v_eq hu, v_eq hv, WithZero.coe_lt_coe, Multiplicative.ofAdd_lt]
    omega
  have key : Valued.v (u - v) = Valued.v u := Valuation.map_sub_eq_of_lt_left _ hlt
  have := ordL_eq_of_v (x := u - v) (k := -ordL u) (by rw [key, v_eq hu])
  simpa using this

theorem ordL_sub_of_ne {u v : L} (hu : u ≠ 0) (hv : v ≠ 0) (h : ordL u ≠ ordL v) :
    ordL (u - v) = min (ordL u) (ordL v) := by
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [ordL_sub_of_lt hu hv h', min_eq_left h'.le]
  · rw [← neg_sub, ordL_neg, ordL_sub_of_lt hv hu h', min_eq_right h'.le]

end Ord

theorem resultant_prod_X_sub_C {R : Type*} [CommRing R] [Nontrivial R] {ι κ : Type*} (A : Finset ι)
    (B : Finset κ) (u : ι → R) (v : κ → R) :
    resultant (∏ i ∈ A, (X - C (u i))) (∏ j ∈ B, (X - C (v j))) = ∏ i ∈ A, ∏ j ∈ B, (u i - v j) := by
  rw [resultant_prod_left A (fun i => X - C (u i)) _ _ (by simp) le_rfl]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ le_rfl, eval_prod]
  simp

theorem ordL_resultant_prod {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {a b : ℕ}
    (u : Fin a → L) (v : Fin b → L) (hu : ∀ i, u i ≠ 0) (hv : ∀ j, v j ≠ 0)
    (h : ∀ i j, ordL (u i) ≠ ordL (v j)) :
    ordL (resultant (∏ i, (X - C (u i))) (∏ j, (X - C (v j)))) =
      ∑ i, ∑ j, min (ordL (u i)) (ordL (v j)) := by
  have hne : ∀ i j, u i - v j ≠ 0 := fun i j hij => h i j (by rw [sub_eq_zero.mp hij])
  rw [resultant_prod_X_sub_C, ordL_prod _ _ fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => hne i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ordL_prod _ _ fun j _ => hne i j]
  exact Finset.sum_congr rfl fun j _ => ordL_sub_of_ne (hu i) (hv j) (h i j)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem absHalf_eq (w : Pl E) (x : w.adicCompletion E) : absHalf w x = qh w ^ (-ordL x) := by
  have key : ∀ (q : ℝ), 0 ≤ q → ∀ k : ℤ, √(q ^ k) = √q ^ k := by
    intro q hq k
    have h1 : q ^ k = (√q ^ k) ^ 2 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, Real.sq_sqrt hq]
    rw [h1, Real.sqrt_sq (zpow_nonneg (Real.sqrt_nonneg q) k)]
  unfold absHalf qh
  rw [key _ (Nat.cast_nonneg _), Complex.ofReal_zpow]

omit [IsCMField E] in

theorem delta_inert (w : Pl E) (hw : ¬ IsSplitAt w) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) :
    delta w μ Q₁ Q₂ = (-qh w) ^ (-ordL (resultant Q₁ Q₂)) := by
  rw [delta, if_neg hw, absHalf_eq, neg_eq_neg_one_mul (qh w), mul_zpow]
  congr 1
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]

def lo {n : ℕ} (k : Fin (n / 2)) : Fin n := ⟨k.val, by have := k.isLt; omega⟩

def hi {n : ℕ} (k : Fin (n / 2)) : Fin n := ⟨n - 1 - k.val, by have := k.isLt; omega⟩

theorem lo_inj {n : ℕ} : Function.Injective (lo (n := n)) := by
  intro a b h
  simp only [lo, Fin.mk.injEq] at h
  exact Fin.ext h

theorem hi_inj {n : ℕ} : Function.Injective (hi (n := n)) := by
  intro a b h
  simp only [hi, Fin.mk.injEq] at h
  have := a.isLt
  have := b.isLt
  exact Fin.ext (by omega)

def midSet (n : ℕ) (mid : Prop) [Decidable mid] : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => mid ∧ n % 2 = 1 ∧ i.val = n / 2

theorem symIdx_eq (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) :
    symIdx n mid s = (s.map ⟨lo, lo_inj⟩ ∪ s.map ⟨hi, hi_inj⟩) ∪ midSet n mid := by
  ext i
  simp only [symIdx, midSet, Finset.mem_union, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
    true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro (⟨h, hs⟩ | ⟨h, hs⟩ | hm)
    · exact Or.inl (Or.inl ⟨_, hs, Fin.ext rfl⟩)
    · refine Or.inl (Or.inr ⟨_, hs, Fin.ext ?_⟩)
      simp only [hi]
      have := i.isLt
      omega
    · exact Or.inr hm
  · rintro ((⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | hm)
    · exact Or.inl ⟨k.isLt, by simpa [lo] using hk⟩
    · have := k.isLt
      refine Or.inr (Or.inl ⟨by simp [hi]; omega, ?_⟩)
      convert hk using 1
      ext
      simp [hi]
      omega
    · exact Or.inr (Or.inr hm)

theorem sum_midSet (n : ℕ) (mid : Prop) [Decidable mid] (F : Fin n → ℤ) :
    ∑ i ∈ midSet n mid, F i = if h : mid ∧ n % 2 = 1 then F ⟨n / 2, by have := h.2; omega⟩ else 0 := by
  split_ifs with h
  · have : midSet n mid = {⟨n / 2, by have := h.2; omega⟩} := by
      ext i
      simp only [midSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨-, -, hi⟩
        exact Fin.ext hi
      · rintro rfl
        exact ⟨h.1, h.2, rfl⟩
    rw [this, Finset.sum_singleton]
  · apply Finset.sum_eq_zero
    intro i hi
    simp only [midSet, Finset.mem_filter] at hi
    exact absurd ⟨hi.2.1, hi.2.2.1⟩ h

theorem sum_symIdx (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) (F : Fin n → ℤ) :
    ∑ i ∈ symIdx n mid s, F i = ∑ k ∈ s, F (lo k) + ∑ k ∈ s, F (hi k) + ∑ i ∈ midSet n mid, F i := by
  rw [symIdx_eq, Finset.sum_union, Finset.sum_union, Finset.sum_map, Finset.sum_map]
  · rfl
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
    rintro _ ⟨a, -, rfl⟩ ⟨b, -, hb⟩
    have := a.isLt
    have := b.isLt
    simp only [lo, hi, Fin.mk.injEq] at hb
    omega
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk, midSet,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rintro _ (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩) ⟨-, h2, h3⟩ <;> have := a.isLt <;> simp [lo, hi] at h3 <;> omega

theorem wexp_lo (n : ℕ) (l : Fin (n / 2) → ℤ) (k : Fin (n / 2)) : wexp n l (lo k) = l k := by
  simp [wexp, lo]

theorem wexp_hi (n : ℕ) (l : Fin (n / 2) → ℤ) (k : Fin (n / 2)) : wexp n l (hi k) = -l k := by
  have := k.isLt
  unfold wexp hi
  rw [dif_neg (by simp; omega), dif_pos (by simp; omega)]
  congr 2
  ext
  simp
  omega

theorem wexp_half (n : ℕ) (l : Fin (n / 2) → ℤ) (h : n % 2 = 1) :
    wexp n l ⟨n / 2, by omega⟩ = 0 := by
  unfold wexp
  rw [dif_neg (by simp), dif_neg (by simp; omega)]

theorem sum_symIdx_wexp (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) (l : Fin (n / 2) → ℤ)
    (G : ℤ → ℤ) :
    ∑ i ∈ symIdx n mid s, G (wexp n l i) =
      ∑ k ∈ s, (G (l k) + G (-l k)) + if mid ∧ n % 2 = 1 then G 0 else 0 := by
  rw [sum_symIdx, sum_midSet, Finset.sum_add_distrib]
  simp only [wexp_lo, wexp_hi]
  congr 1
  split_ifs with h
  · rw [wexp_half n l h.2]
  · rfl

theorem min_four {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min x y + min x (-y) + (min (-x) y + min (-x) (-y)) = -2 * max x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_right (by omega : -y ≤ x), min_eq_left (by omega : -x ≤ y),
      min_eq_right (by omega : -y ≤ -x), max_eq_right h]
    ring
  · rw [min_eq_right h, min_eq_right (by omega : -y ≤ x), min_eq_left (by omega : -x ≤ y),
      min_eq_left (by omega : -x ≤ -y), max_eq_left h]
    ring

theorem sum_min_wexp (n a : ℕ) (ha : a ≤ n) (l : Fin (n / 2) → ℤ) (hl : ∀ k, 0 ≤ l k)
    (s : Finset (Fin (n / 2))) :
    ∑ i ∈ symIdx n (a % 2 = 1) s, ∑ j ∈ symIdx n ((n - a) % 2 = 1) sᶜ, min (wexp n l i) (wexp n l j) =
      vRes n a l s := by
  have key : ∀ c : ℤ, ∑ j ∈ symIdx n ((n - a) % 2 = 1) sᶜ, min c (wexp n l j) =
      ∑ k ∈ sᶜ, (min c (l k) + min c (-l k)) + if (n - a) % 2 = 1 ∧ n % 2 = 1 then min c 0 else 0 :=
    fun c => sum_symIdx_wexp n _ sᶜ l (fun y => min c y)
  have outer := sum_symIdx_wexp n (a % 2 = 1) s l
    (fun x => ∑ j ∈ symIdx n ((n - a) % 2 = 1) sᶜ, min x (wexp n l j))
  rw [outer]
  simp only [key]
  have e1 : ∀ k ∈ s, (∑ k' ∈ sᶜ, (min (l k) (l k') + min (l k) (-l k')) +
      (if (n - a) % 2 = 1 ∧ n % 2 = 1 then min (l k) 0 else 0)) +
      (∑ k' ∈ sᶜ, (min (-l k) (l k') + min (-l k) (-l k')) +
      (if (n - a) % 2 = 1 ∧ n % 2 = 1 then min (-l k) 0 else 0)) =
      ∑ k' ∈ sᶜ, -2 * max (l k) (l k') + (if (n - a) % 2 = 1 ∧ n % 2 = 1 then -l k else 0) := by
    intro k _
    rw [add_add_add_comm, ← Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun k' _ => min_four (hl k) (hl k')
    · have := hl k
      split_ifs
      · rw [min_eq_right this, min_eq_left (by omega)]
        ring
      · ring
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
  have e2 : ∑ k ∈ sᶜ, (min 0 (l k) + min 0 (-l k)) = -∑ k ∈ sᶜ, l k := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      have := hl k
      rw [min_eq_left this, min_eq_right (by omega)]
      ring
  rw [e2, vRes, Finset.mul_sum]
  simp only [min_self, add_zero, ite_self]
  by_cases hn : n % 2 = 1
  · by_cases ha2 : a % 2 = 1
    · have : ¬ (n - a) % 2 = 1 := by omega
      simp [hn, ha2, this]
      simp only [Finset.mul_sum]
      ring
    · have : (n - a) % 2 = 1 := by omega
      simp [hn, ha2, this]
      simp only [Finset.mul_sum]
      ring
  · simp [hn, Finset.mul_sum]

theorem mem_rev {n : ℕ} {mid : Prop} [Decidable mid] {s : Finset (Fin (n / 2))} {i : Fin n}
    (h : i ∈ symIdx n mid s) : i.rev ∈ symIdx n mid s := by
  simp only [symIdx, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hm, ho, he⟩
  · right; left
    refine ⟨by omega, ?_⟩
    convert h2 using 2
    omega
  · left
    refine ⟨by omega, ?_⟩
    convert h2 using 2
    omega
  · right; right
    exact ⟨hm, ho, by omega⟩

theorem orderEmb_rev {n a : ℕ} (S : Finset (Fin n)) (hS : ∀ i ∈ S, i.rev ∈ S) (h : S.card = a) (i : Fin a) :
    S.orderEmbOfFin h i.rev = (S.orderEmbOfFin h i).rev := by
  have key : (fun j : Fin a => (S.orderEmbOfFin h j.rev).rev) = S.orderEmbOfFin h := by
    apply Finset.orderEmbOfFin_unique h
    · intro j
      exact hS _ (Finset.orderEmbOfFin_mem S h _)
    · intro j k hjk
      simp only
      rw [Fin.rev_lt_rev]
      exact (S.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.mpr hjk)
  have := congrFun key i.rev
  simp only [Fin.rev_rev] at this
  rw [← this]

theorem sub_rev_eq_wexp {n : ℕ} (x : Fin n → ℤ) (p : Fin n) : x p - x p.rev = wexp n (lOf x) p := by
  unfold wexp lOf
  split_ifs with h1 h2
  · congr 2
    ext; simp; omega
  · rw [neg_sub]
    congr 2
    · ext; simp; omega
    · ext; simp; omega
  · have : p.rev = p := by ext; simp; omega
    rw [this, sub_self]

theorem nv_restr_eq {n a : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) (hS : ∀ i ∈ S, i.rev ∈ S) (h : S.card = a)
    (i : Fin a) : nv (restr x S h) i = x (S.orderEmbOfFin h i) - x (S.orderEmbOfFin h i).rev := by
  simp only [nv, restr, orderEmb_rev S hS h]

theorem sum_nv_restr {n a : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) (hS : ∀ i ∈ S, i.rev ∈ S)
    (h : S.card = a) (G : ℤ → ℤ) :
    ∑ i : Fin a, G (nv (restr x S h) i) = ∑ p ∈ S, G (wexp n (lOf x) p) := by
  simp only [nv_restr_eq x S hS h, sub_rev_eq_wexp]
  conv_rhs => rw [← Finset.image_orderEmbOfFin_univ S h]
  rw [Finset.sum_image (fun _ _ _ _ e => (S.orderEmbOfFin h).injective e)]

theorem symIdx_disj {n a : ℕ} (ha : a ≤ n) (s : Finset (Fin (n / 2))) {p : Fin n}
    (h₁ : p ∈ symIdx n (a % 2 = 1) s) (h₂ : p ∈ symIdx n ((n - a) % 2 = 1) sᶜ) : False := by
  simp only [symIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl] at h₁ h₂
  rcases h₁ with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨hm, ho, he⟩ <;>
    rcases h₂ with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨hm', ho', he'⟩
  all_goals first | omega | exact h2' h1'

theorem lOf_pos {n : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) (k : Fin (n / 2)) : 0 < lOf x k := by
  unfold lOf
  apply sub_pos.mpr
  apply hx
  rw [Fin.lt_def]
  simp
  omega

end V1

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem strictAnti_sub_rev {n : ℕ} (x : Fin n → ℤ) (hx : StrictAnti x) :
    StrictAnti (fun p : Fin n => x p - x p.rev) := by
  intro p q hpq
  have h1 := hx hpq
  have h2 := hx (Fin.rev_lt_rev.mpr hpq)
  simp only
  linarith

open V1 in

theorem inert_delta_first_case_eq_power (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (x : Fin n → ℤ) (hx : StrictAnti x)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) (s : Finset (Fin (n / 2))) (hA : CaseA w n a x Q₁ Q₂ s) :
    delta w 1 Q₁ Q₂ = (-qh w) ^ (-vRes n a (lOf x) s) := by
  obtain ⟨-, -, -, h₁, h₂, ⟨u, rfl, hu⟩, ⟨v, rfl, hv⟩⟩ := hA
  set S₁ := symIdx n (a % 2 = 1) s with hS₁def
  set S₂ := symIdx n ((n - a) % 2 = 1) sᶜ with hS₂def
  have hS₁ : ∀ p ∈ S₁, p.rev ∈ S₁ := fun p hp => mem_rev hp
  have hS₂ : ∀ p ∈ S₂, p.rev ∈ S₂ := fun p hp => mem_rev hp
  have hu' : ∀ i, ordL (u i) = wexp n (lOf x) (S₁.orderEmbOfFin h₁ i) := fun i => by
    rw [(hu i).2, nv_restr_eq x S₁ hS₁ h₁, sub_rev_eq_wexp]
  have hv' : ∀ j, ordL (v j) = wexp n (lOf x) (S₂.orderEmbOfFin h₂ j) := fun j => by
    rw [(hv j).2, nv_restr_eq x S₂ hS₂ h₂, sub_rev_eq_wexp]
  have hinj : Function.Injective (wexp n (lOf x)) := by
    intro p q hpq
    rw [← sub_rev_eq_wexp x p, ← sub_rev_eq_wexp x q] at hpq
    exact (strictAnti_sub_rev x hx).injective hpq
  have hne : ∀ i j, ordL (u i) ≠ ordL (v j) := by
    intro i j h
    rw [hu', hv'] at h
    exact symIdx_disj ha s (Finset.orderEmbOfFin_mem S₁ h₁ i)
      (by rw [hinj h]; exact Finset.orderEmbOfFin_mem S₂ h₂ j)
  have hu2 : ∀ i, ordL (u i) = nv (restr x S₁ h₁) i := fun i => (hu i).2
  have hv2 : ∀ j, ordL (v j) = nv (restr x S₂ h₂) j := fun j => (hv j).2
  have key : ordL (resultant (∏ i, (X - C (u i))) (∏ j, (X - C (v j)))) = vRes n a (lOf x) s := by
    rw [ordL_resultant_prod u v (fun i => (hu i).1) (fun j => (hv j).1) hne,
      ← sum_min_wexp n a ha (lOf x) (fun k => (lOf_pos hx k).le) s]
    simp only [hu2, hv2]
    refine Eq.trans ?_ (sum_nv_restr x S₁ hS₁ h₁ (fun t => ∑ q ∈ S₂, min t (wexp n (lOf x) q)))
    refine Finset.sum_congr rfl fun i _ => ?_
    exact sum_nv_restr x S₂ hS₂ h₂ (fun t => min (nv (restr x S₁ h₁) i) t)
  rw [delta_inert w hw, key]

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
