import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare.SqCount

theorem sq_mul_unique {k : Type} [Field k] {a b c d : k[X]} (ha : a.Monic) (hc : c.Monic)
    (hb : Squarefree b) (hd : Squarefree d) (h : a ^ 2 * b = c ^ 2 * d) : a = c ∧ b = d := by
  obtain ⟨a1, c1, e, hco, rfl, rfl⟩ : ∃ a1 c1 e : k[X], IsCoprime a1 c1 ∧ a = e * a1 ∧ c = e * c1 := by
    obtain ⟨a1, c1, h1, h2, h3⟩ := extract_gcd a c
    exact ⟨a1, c1, GCDMonoid.gcd a c, (gcd_isUnit_iff _ _).1 h3, h1, h2⟩
  have he : e ≠ 0 := left_ne_zero_of_mul ha.ne_zero
  have h' : a1 ^ 2 * b = c1 ^ 2 * d := by
    apply mul_left_cancel₀ (pow_ne_zero 2 he)
    linear_combination h
  have u1 : IsUnit a1 := by
    apply hd
    rw [← sq]
    exact (hco.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left ⟨b, h'.symm⟩
  have u2 : IsUnit c1 := by
    apply hb
    rw [← sq]
    exact (hco.symm.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left ⟨d, h'⟩
  have hac : e * a1 = e * c1 :=
    eq_of_monic_of_associated ha hc ((associated_mul_unit_left e a1 u1).trans (associated_mul_unit_left e c1 u2).symm)
  refine ⟨hac, ?_⟩
  rw [hac] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 hc.ne_zero) h

theorem exists_sq_mul {k : Type} [Field k] {f : k[X]} (hf : f.Monic) :
    ∃ a b : k[X], a.Monic ∧ b.Monic ∧ Squarefree b ∧ f = a ^ 2 * b := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  by_cases hs : Squarefree f
  · exact ⟨1, f, monic_one, hf, hs, by simp⟩
  obtain ⟨x, hx, hu⟩ : ∃ x, x * x ∣ f ∧ ¬ IsUnit x := by
    by_contra hc
    exact hs fun x hx => by_contra fun hu => hc ⟨x, hx, hu⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hf.ne_zero (by simpa using hx)
  have hy : (normalize x).Monic := monic_normalize hx0
  have hass : Associated (normalize x) x := normalize_associated x
  obtain ⟨h, rfl⟩ := (hass.mul_mul hass).dvd.trans hx
  have hh : h.Monic := (hy.mul hy).of_mul_monic_left hf
  have hpos : 0 < (normalize x).natDegree :=
    natDegree_pos_of_not_isUnit_of_dvd_monic hy (fun hu' => hu (hass.isUnit hu')) dvd_rfl
  rw [(hy.mul hy).natDegree_mul hh, hy.natDegree_mul hy] at hn
  obtain ⟨a, b, ha, hb, hsq, rfl⟩ := ih h.natDegree (by omega) hh rfl
  exact ⟨normalize x * a, b, hy.mul ha, hb, hsq, by ring⟩

variable (g : ℕ) [Fact g.Prime]

noncomputable def monicSet (N : ℕ) : Finset (ZMod g)[X] :=
  Finset.univ.image fun c : Fin N → ZMod g => (X ^ N + ∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X])

variable {g}

theorem mem_monicSet {N : ℕ} {f : (ZMod g)[X]} : f ∈ monicSet g N ↔ f.Monic ∧ f.natDegree = N := by
  unfold monicSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨c, -, rfl⟩
    have hlt : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < (N : WithBot ℕ) := degree_sum_fin_lt c
    refine ⟨monic_X_pow_add hlt, ?_⟩
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  · rintro ⟨hm, rfl⟩
    refine ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    conv_rhs => rw [hm.as_sum]
    rw [Finset.sum_range fun i => C (f.coeff i) * X ^ i]

theorem card_monicSet (N : ℕ) : (monicSet g N).card = g ^ N := by
  unfold monicSet
  rw [Finset.card_image_of_injective]
  · simp [ZMod.card]
  · intro c d h
    have h' := add_left_cancel h
    funext i
    have := congrArg (fun p => coeff p i) h'
    simpa [finset_sum_coeff, coeff_X_pow, Fin.val_inj] using this

theorem monic_divX {k : Type} [Field k] {a : k[X]} (ha : a.Monic) (hd : 1 ≤ a.natDegree) : a.divX.Monic := by
  rw [Monic, leadingCoeff, natDegree_divX_eq_natDegree_tsub_one, coeff_divX, Nat.sub_add_cancel hd]
  exact ha

theorem card_zero_const (n : ℕ) : ((monicSet g (n + 1)).filter fun f => f.coeff 0 = 0).card ≤ g ^ n := by
  rw [← card_monicSet]
  refine Finset.card_le_card_of_injOn divX ?_ ?_
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_monicSet, Finset.mem_coe] at hf ⊢
    refine ⟨monic_divX hf.1.1 (by omega), ?_⟩
    rw [natDegree_divX_eq_natDegree_tsub_one]; omega
  · intro f hf f' hf' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_monicSet] at hf hf'
    rw [← divX_mul_X_add f, ← divX_mul_X_add f', h, hf.2, hf'.2]

theorem card_not_squarefree (n : ℕ) : ((monicSet g (n + 1)).filter fun f => ¬ Squarefree f).card ≤ g ^ n := by
  rcases n with _ | n
  · rw [Finset.filter_eq_empty_iff.2]
    · simp
    · intro f hf
      rw [mem_monicSet] at hf
      rw [not_not]
      exact (irreducible_of_degree_eq_one (by rw [degree_eq_natDegree hf.1.ne_zero, hf.2]; rfl)).squarefree
  have hc : ((Finset.univ : Finset (ZMod g)) ×ˢ monicSet g n).card = g ^ (n + 1) := by
    rw [Finset.card_product, card_monicSet, Finset.card_univ, ZMod.card, pow_succ']
  rw [← hc]
  refine Finset.card_le_card_of_forall_subsingleton
    (fun f p => ∃ a b : (ZMod g)[X], a.Monic ∧ Squarefree b ∧ p.2 = a ^ 2 * b ∧ f = (a * X + C p.1) ^ 2 * b) ?_ ?_
  · intro f hf
    rw [Finset.mem_filter, mem_monicSet] at hf
    obtain ⟨⟨hm, hd⟩, hs⟩ := hf
    obtain ⟨a, b, ha, hb, hsq, rfl⟩ := exists_sq_mul hm
    have h1 : 1 ≤ a.natDegree := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      rw [ha.natDegree_eq_zero] at h0
      subst h0
      exact hs (by simpa using hsq)
    have ha' := monic_divX ha h1
    refine ⟨(a.coeff 0, a.divX ^ 2 * b), ?_, a.divX, b, ha', hsq, rfl, by rw [divX_mul_X_add]⟩
    rw [Finset.mem_product, mem_monicSet]
    refine ⟨Finset.mem_univ _, (ha'.pow 2).mul hb, ?_⟩
    rw [(ha.pow 2).natDegree_mul hb, ha.natDegree_pow] at hd
    show (a.divX ^ 2 * b).natDegree = n
    rw [(ha'.pow 2).natDegree_mul hb, ha'.natDegree_pow, natDegree_divX_eq_natDegree_tsub_one]
    omega
  · rintro p - f ⟨-, a, b, ha, hb, h1, rfl⟩ f' ⟨-, c, d, hc, hd, h2, rfl⟩
    obtain ⟨rfl, rfl⟩ := sq_mul_unique ha hc hb hd (h1.symm.trans h2)
    rfl

end GlobalTheory.BadShare.SqCount

open GlobalTheory.BadShare.SqCount in

theorem GlobalTheory.BadShare.card_sqSet_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 ≤ N →
    (g : ℝ) ^ N - 2 * (g : ℝ) ^ (N - 1) ≤ ((sqSet g N).card : ℝ) := by
  intro g _ N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hsub : monicSet g (n + 1) ⊆ sqSet g (n + 1) ∪ (((monicSet g (n + 1)).filter fun f => f.coeff 0 = 0) ∪
      ((monicSet g (n + 1)).filter fun f => ¬ Squarefree f)) := by
    intro f hf
    simp only [Finset.mem_union, Finset.mem_filter, mem_sqSet]
    have := mem_monicSet.1 hf
    tauto
  have h1 := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (card_zero_const n) (card_not_squarefree n))) _))
  rw [card_monicSet] at h1
  have h2 : ((g : ℝ)) ^ (n + 1) ≤ ((sqSet g (n + 1)).card : ℝ) + ((g : ℝ) ^ n + (g : ℝ) ^ n) := by exact_mod_cast h1
  rw [Nat.add_sub_cancel]
  linarith
