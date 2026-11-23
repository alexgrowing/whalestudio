import Formalism.LocalToGlobal.CharacterGerms.RowTieFB

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace ValuationNonnegativity

variable {C : Type} [Field C] {V : VF C}

theorem valuation_nonneg_iff {a : C} : V.Ge 0 a ↔ 0 ≤ V.v a := by
  unfold VF.Ge
  rw [WithTop.coe_zero]

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM
  simp

theorem mm_of_ge_one {a : C} (h : V.Ge 1 a) : V.MM a := by
  unfold VF.MM
  unfold VF.Ge at h
  exact lt_of_lt_of_le (by exact_mod_cast one_pos) h

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_neg {a : C} (ha : V.MM a) : V.MM (-a) := by
  unfold VF.MM at *
  rwa [V.v.map_neg]

theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]
  exact mm_add ha (mm_neg hb)

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x => V.MM x) (fun _ _ => mm_add) mm_zero h

theorem mm_mul_int {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  have h0 := valuation_nonneg_iff.mp ha
  unfold VF.MM at *
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left h0)

theorem v_pow_coe {a : C} {t : ℝ} (h : V.v a = (t : WithTop ℝ)) (k : ℕ) :
    V.v (a ^ k) = (((k : ℝ) * t : ℝ) : WithTop ℝ) := by
  rw [V.v.map_pow, h, ← WithTop.coe_nsmul, nsmul_eq_mul]

theorem mm_of_pow {a : C} {n : ℕ} (h : V.MM (a ^ n)) : V.MM a := by
  unfold VF.MM at *
  rw [V.v.map_pow] at h
  by_contra hle
  push_neg at hle
  exact absurd h (not_lt.mpr (nsmul_nonpos hle n))

theorem mm_pow {a : C} (ha : V.MM a) {n : ℕ} (hn : n ≠ 0) : V.MM (a ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold VF.MM at *
  rw [V.v.map_pow, succ_nsmul]
  exact lt_of_lt_of_le ha (le_add_of_nonneg_left (nsmul_nonneg ha.le m))

theorem valuation_nonneg_of_pow {a : C} {n : ℕ} (h : V.Ge 0 (a ^ n)) (hn : n ≠ 0) : V.Ge 0 a := by
  rw [valuation_nonneg_iff] at *
  rw [V.v.map_pow] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_contra hlt
  push_neg at hlt
  rw [succ_nsmul] at h
  have h1 : m • V.v a ≤ 0 := nsmul_nonpos hlt.le m
  exact absurd h (not_le.mpr (lt_of_le_of_lt (le_of_le_of_eq (add_le_add h1 le_rfl) (zero_add _)) hlt))

theorem valuation_nonneg_div {x y : C} (hy : y ≠ 0) (h : V.v y ≤ V.v x) : V.Ge 0 (x / y) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (fun h' => hy ((V.v.top_iff).mp h'))
  have hx : x = (x / y) * y := by field_simp
  rw [valuation_nonneg_iff]
  by_contra hlt
  push_neg at hlt
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have h2 : V.v x = ((s + r : ℝ) : WithTop ℝ) := by
    rw [hx, V.v.map_mul, ← hs, ← hr, WithTop.coe_add]
  rw [← hs] at hlt
  rw [h2, ← hr] at h
  have h3 : s < 0 := by exact_mod_cast hlt
  have h4 : r ≤ s + r := by exact_mod_cast h
  linarith

private theorem v_natCast_nonneg' (n : ℕ) : 0 ≤ V.v (n : C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    refine le_trans (le_min ih ?_) (V.v.map_add _ _)
    rw [V.v.map_one]

theorem frob2 {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.MM ((a + b) ^ V.l - a ^ V.l - b ^ V.l) := by
  have hl := V.l_prime
  obtain ⟨k, hk⟩ : ∃ k, V.l = k + 2 := ⟨V.l - 2, by have := hl.two_le; omega⟩
  have hl' : (k + 2).Prime := hk ▸ hl
  have hint : ∀ m n : ℕ, V.Ge 0 (a ^ m * b ^ n) := by
    intro m n
    rw [valuation_nonneg_iff, V.v.map_mul, V.v.map_pow, V.v.map_pow]
    exact add_nonneg (nsmul_nonneg (valuation_nonneg_iff.mp ha) m) (nsmul_nonneg (valuation_nonneg_iff.mp hb) n)
  have hch : ∀ m ∈ Finset.range (k + 1),
      V.MM (a ^ (m + 1) * b ^ (k + 2 - (m + 1)) * ((k + 2).choose (m + 1) : C)) := by
    intro m hm
    rw [Finset.mem_range] at hm
    apply mm_mul_int (hint _ _)
    obtain ⟨t, ht⟩ : (k + 2) ∣ (k + 2).choose (m + 1) := hl'.dvd_choose_self (by omega) (by omega)
    rw [ht, Nat.cast_mul, ← hk]
    unfold VF.MM
    rw [V.v.map_mul, V.v_l]
    exact lt_of_lt_of_le (by exact_mod_cast one_pos) (le_add_of_nonneg_right (v_natCast_nonneg' t))
  have hexp : (a + b) ^ V.l - a ^ V.l - b ^ V.l =
      ∑ m ∈ Finset.range (k + 1), a ^ (m + 1) * b ^ (k + 2 - (m + 1)) * ((k + 2).choose (m + 1) : C) := by
    rw [hk, add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, mul_one, Nat.sub_zero, Nat.choose_zero_right, Nat.choose_self,
      Nat.cast_one, Nat.sub_self]
    ring
  rw [hexp]
  exact mm_sum hch

theorem frob_sum {ι : Type*} (s : Finset ι) (f : ι → C) (hf : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.MM ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_pow V.l_prime.ne_zero, sub_zero]; exact mm_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs : V.Ge 0 (∑ j ∈ s, f j) := VF.Ge.sum fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have h1 := frob2 (hf i (Finset.mem_insert_self i s)) hs
    have h2 := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have e : (f i + ∑ j ∈ s, f j) ^ V.l - (f i ^ V.l + ∑ j ∈ s, f j ^ V.l) =
        ((f i + ∑ j ∈ s, f j) ^ V.l - f i ^ V.l - (∑ j ∈ s, f j) ^ V.l) +
          ((∑ j ∈ s, f j) ^ V.l - ∑ j ∈ s, f j ^ V.l) := by ring
    rw [e]; exact mm_add h1 h2

theorem exists_rel {N m : ℕ} (hm : m < N) (B : Fin N → Fin m → C) :
    ∃ β : Fin N → C, (∀ ν, V.Ge 0 (β ν)) ∧ (∃ ν, ¬ V.MM (β ν)) ∧ ∀ r, ∑ ν, β ν * B ν r = 0 := by
  let f : (Fin N → C) →ₗ[C] (Fin m → C) := Matrix.vecMulLinear (Matrix.of B)
  have hk : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hm)
  obtain ⟨β, hβ, hne⟩ := (Submodule.ne_bot_iff _).mp hk
  have hrel : ∀ r, ∑ ν, β ν * B ν r = 0 := fun r => by
    have := congrFun (LinearMap.mem_ker.mp hβ) r
    simpa [f, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct] using this
  obtain ⟨ν1, hν1⟩ : ∃ ν, β ν ≠ 0 := by
    by_contra hc; push Not at hc; exact hne (funext hc)
  obtain ⟨ν0, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun ν => V.v (β ν))
    ⟨ν1, Finset.mem_univ _⟩
  have h0 : β ν0 ≠ 0 := by
    intro h
    have := hmin ν1 (Finset.mem_univ _)
    rw [h, V.v.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact hν1 this
  refine ⟨fun ν => β ν / β ν0, fun ν => valuation_nonneg_div h0 (hmin ν (Finset.mem_univ _)), ⟨ν0, ?_⟩, fun r => ?_⟩
  · show ¬ V.MM (β ν0 / β ν0)
    rw [div_self h0]; unfold VF.MM; rw [V.v.map_one]; exact lt_irrefl 0
  · simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hrel r, zero_div]

variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

theorem independence_bound_of_span_raw [IsAlgClosed C] (X : Cart V d I J) (a : ZMod d) (m : ℕ)
    (hR2 : ∀ (w : I → C) (x : ℕ → I ⊕ J → C), X.Good a w x → (∀ q, V.MM (X.c0' x q)) → ∀ c, V.MM (w c))
    (e : Fin m → J → C)
    (hspan : ∀ (w : I → C) (x : ℕ → I ⊕ J → C), X.Good a w x → (∀ c, V.MM (X.V2 x c)) →
      ∃ b : Fin m → C, ∀ q, V.MM (X.c0' x q ^ V.l - ∑ r, b r * e r q))
    (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C) (hg : ∀ ν, X.Good a (w ν) (x ν))
    (hV : ∀ ν c, V.MM (X.V2 (x ν) c)) (hind : IndepMod V w) : N ≤ m := by
  by_contra hN; push Not at hN
  choose b hb using fun ν => hspan (w ν) (x ν) (hg ν) (hV ν)
  obtain ⟨β, hβi, ⟨ν0, hν0⟩, hrel⟩ := exists_rel (V := V) hN b
  have hl2 : 0 < V.l ^ 2 := pow_pos V.l_prime.pos 2
  choose c hc using fun ν => IsAlgClosed.exists_pow_nat_eq (β ν) hl2
  have hci : ∀ ν, V.Ge 0 (c ν) := fun ν => valuation_nonneg_of_pow (by rw [hc ν]; exact hβi ν) hl2.ne'
  have hG := Cart.Good.comb (X := X) Finset.univ (co := c) (fun ν _ => hci ν) (fun ν _ => hg ν)
  have hz : ∀ ν q, V.Ge 0 (X.c0' (x ν) q) := fun ν q => (hg ν).c0'_int q
  have hc0 : ∀ q, V.MM (X.c0' (∑ ν, teich V.l (c ν) (x ν)) q) := by
    intro q
    rw [Cart.c0'_comb]
    apply mm_of_pow (n := V.l)
    have h1 := frob_sum Finset.univ (fun ν => c ν ^ V.l * X.c0' (x ν) q)
      (fun ν _ => VF.Ge.mul_int ((hci ν).pow _) (hz ν q))
    have e1 : ∀ ν, (c ν ^ V.l * X.c0' (x ν) q) ^ V.l = β ν * X.c0' (x ν) q ^ V.l := by
      intro ν; rw [mul_pow, ← pow_mul, ← hc ν, sq]
    simp only [e1] at h1
    have h2 : V.MM (∑ ν, β ν * (X.c0' (x ν) q ^ V.l - ∑ r, b ν r * e r q)) :=
      mm_sum fun ν _ => mm_mul_int (hβi ν) (hb ν q)
    have h3 : ∑ ν, β ν * (∑ r, b ν r * e r q) = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun r _ => ?_
      calc ∑ ν, β ν * (b ν r * e r q) = (∑ ν, β ν * b ν r) * e r q := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by rw [hrel r, zero_mul]
    have e2 : (∑ ν, c ν ^ V.l * X.c0' (x ν) q) ^ V.l =
        ((∑ ν, c ν ^ V.l * X.c0' (x ν) q) ^ V.l - ∑ ν, β ν * X.c0' (x ν) q ^ V.l) +
          ∑ ν, β ν * (X.c0' (x ν) q ^ V.l - ∑ r, b ν r * e r q) + ∑ ν, β ν * (∑ r, b ν r * e r q) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [e2, h3, add_zero]
    exact mm_add h1 h2
  have hw := hR2 _ _ hG hc0
  have hcm := hind c hci (fun y => by
    have := hw y
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this)
  apply hν0
  rw [← hc ν0]
  exact mm_pow (hcm ν0) hl2.ne'

theorem even_val_add_two {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) :
    Even (a + 2).val ↔ Even a.val := by
  have h2d : 2 ∣ d := even_iff_two_dvd.mp hd
  rw [ZMod.val_add, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2d]
  have h2 : (2 : ZMod d).val % 2 = 0 := by
    rw [show (2 : ZMod d) = ((2 : ℕ) : ZMod d) by norm_num, ZMod.val_natCast, Nat.mod_mod_of_dvd _ h2d]
  omega

end ValuationNonnegativity

section Closed

variable {C : Type} [Field C]

def CoefficientIdentityCondition : Prop :=
  AllFB fun C _ V _ I _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, X.AltC → ∀ g a, X.big g a →
    ∃ M : JJ I g → JJ I g → C, ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ c1 : JJ I g → C, (∀ q, X.ty (1 - g) q ≠ a + 2 → c1 q = 0) ∧
        ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ q', c1 q' * M q' q)

def IndependenceSpanCondition : Prop :=
  AllFB fun C _ V _ I _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, X.AltC → ∀ g a, X.big g a →
    ∃ e : Fin X.j' → JJ I g → C, ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ b : Fin X.j' → C, ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ r, b r * e r q)

theorem independence_bound_of_span (h : IndependenceSpanCondition) : IndependenceBoundAllCharts := by
  intro C _ _ V O _ _ dd Y d _ I _ p hrk H hR2 hAlt g a hbig N w x hg hV hind
  have := Y.algClosed
  obtain ⟨e, he⟩ := h C V O dd Y d I p hrk H hAlt g a hbig
  exact ValuationNonnegativity.independence_bound_of_span_raw (RawChart.cart (H g)) a _ (hR2 hAlt g a hbig) e he N w x hg hV hind

theorem independence_span_of_coefficient (h : CoefficientIdentityCondition) : IndependenceSpanCondition := by
  intro C _ _ V O _ _ dd Y d _ I _ p hrk H hAlt g a hbig
  have key : ∀ g' : Fin 2, (Y.raw p).big g' a → (Y.raw p).big g' (a + 2) := by
    obtain ⟨hd, hpar⟩ := hAlt
    have hev := ValuationNonnegativity.even_val_add_two hd a
    have e1 : ∀ b, (Y.raw p).big 1 b ↔ ¬ (Y.raw p).big 0 b := fun b => by
      simpa using hrk.big_compl 0 b
    intro g' hb
    fin_cases g'
    · exact (hpar (a + 2)).2 (hev.2 ((hpar a).1 hb))
    · simp only [Fin.mk_one] at hb ⊢
      rw [e1, hpar] at hb ⊢
      rwa [hev]
  have hsmall : ¬ (Y.raw p).big (1 - g) (a + 2) := fun h2 => (hrk.big_compl g (a + 2)).1 h2 (key g hbig)
  have hcard : Fintype.card {q : JJ I g // (Y.raw p).ty (1 - g) q = a + 2} = (Y.raw p).j' := by
    rw [Fintype.card_subtype]; exact hrk.rk_small (1 - g) (a + 2) hsmall
  obtain ⟨M, hM⟩ := h C V O dd Y d I p hrk H hAlt g a hbig
  let σ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun r => M (σ r).1, fun w x hg hV => ?_⟩
  obtain ⟨c1, hsupp, hc1⟩ := hM w x hg hV
  refine ⟨fun r => c1 (σ r).1, fun q => ?_⟩
  have hsum : ∑ q', c1 q' * M q' q = ∑ r, c1 (σ r).1 * M (σ r).1 q := by
    rw [← Finset.sum_filter_of_ne (p := fun q' => (Y.raw p).ty (1 - g) q' = a + 2)
      (fun q' _ hne => by
        by_contra hq
        exact hne (by rw [hsupp q' hq, zero_mul]))]
    rw [Finset.sum_subtype (Finset.univ.filter fun q' => (Y.raw p).ty (1 - g) q' = a + 2)
      (p := fun q' => (Y.raw p).ty (1 - g) q' = a + 2) (fun q' => by simp)]
    exact (Equiv.sum_comp σ (fun s => c1 s.1 * M s.1 q)).symm
  rw [← hsum]
  exact hc1 q

theorem independence_bound_of_coefficient (h : CoefficientIdentityCondition) : IndependenceBoundAllCharts :=
  independence_bound_of_span (independence_span_of_coefficient h)

end Closed

end Formalism.L2.FormalSeriesBounds
