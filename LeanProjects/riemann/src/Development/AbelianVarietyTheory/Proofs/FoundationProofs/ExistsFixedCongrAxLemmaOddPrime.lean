import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeNatCastIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsChooseSmallPadicValAxInductionStatement

open Polynomial

namespace GlobalTheory.AxSen

section Step

variable {K : Type} [Field K] {A : ValuationSubring K} {ϖ : K}

theorem ge_coeff_prod (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1) {q : ℚ} (s : Multiset K) (hs : ∀ d ∈ s, Ge A ϖ d q) (k : ℕ) :
    Ge A ϖ ((s.map fun d => X + C d).prod.coeff k) (((s.card : ℚ) - k) * q) := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
    rcases k with _ | k
    · have := (ge_natCast_iff (A := A) h0 h1 (w := 1) (m := 0)).mpr ⟨1, A.one_mem, by simp⟩
      simpa using this
    · simpa [coeff_one] using ge_zero _
  | cons d s ih =>
    have hd := hs d (Multiset.mem_cons_self _ _)
    have ih' := ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, coeff_add, coeff_C_mul, Multiset.card_cons]
    refine Ge.add ?_ ((hd.mul h0 h1 (ih' k)).mono (le_of_eq (by push_cast; ring)))
    rcases k with _ | k
    · rw [coeff_X_mul_zero]; exact ge_zero _
    · rw [coeff_X_mul]; exact (ih' k).mono (le_of_eq (by push_cast; ring))

theorem exists_ge_of_prod (s : Multiset K) (hs : s ≠ 0) {q : ℚ} (h : Ge A ϖ s.prod (q * s.card)) :
    ∃ d ∈ s, Ge A ϖ d q := by
  classical
  obtain ⟨d, hd, hmin⟩ := Finset.exists_min_image s.toFinset A.valuation (Multiset.toFinset_nonempty.mpr hs)
  refine ⟨d, Multiset.mem_toFinset.mp hd, Ge.root (Multiset.card_pos.mpr hs) (h.of_le ?_)⟩
  rw [map_pow, map_multiset_prod, ← Multiset.card_map A.valuation s]
  refine Multiset.pow_card_le_prod fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  exact hmin y (Multiset.mem_toFinset.mpr hy)

theorem exists_root_hasseDeriv [IsAlgClosed K] [CharZero K] (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1) (T : Finset K) (α : K) {a : ℚ}
    (hT : ∀ t ∈ T, Ge A ϖ (α - t) a) {j e : ℕ} (hj : j < T.card)
    (hc : A.valuation ϖ ^ e ≤ A.valuation ((T.card.choose j : ℕ) : K)) :
    ∃ β ∈ (hasseDeriv j (∏ t ∈ T, (X - C t))).roots, Ge A ϖ (α - β) (a - e / ((T.card - j : ℕ) : ℚ)) := by
  set P : K[X] := ∏ t ∈ T, (X - C t) with hP
  have hPm : P.Monic := monic_prod_of_monic _ _ fun t _ => monic_X_sub_C t
  have hPd : P.natDegree = T.card := by simp [hP]
  set Q := hasseDeriv j P with hQ
  have hQd : Q.natDegree = T.card - j := by rw [hQ, natDegree_hasseDeriv, hPd]
  have hlc : Q.leadingCoeff = ((T.card.choose j : ℕ) : K) := by
    rw [leadingCoeff, hQd, hQ, hasseDeriv_coeff, Nat.sub_add_cancel hj.le, ← hPd, hPm.coeff_natDegree, mul_one]
  have hcard : Q.roots.card = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hev : Q.eval α = ((T.val.map fun t => α - t).map fun d => X + C d).prod.coeff j := by
    rw [hQ, ← taylor_coeff, taylor_apply, hP, prod_comp, Multiset.map_map]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    simp [add_sub_assoc]
  have hge := ge_coeff_prod h0 h1 (T.val.map fun t => α - t) (q := a) (by
    intro d hd
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hd
    exact hT t ht) j
  rw [← hev, ← hfac, eval_mul, eval_C, hlc, eval_multiset_prod, Multiset.map_map] at hge
  have hdiv := hge.div h0 h1 hc
  have hpos : 0 < T.card - j := Nat.sub_pos_of_lt hj
  obtain ⟨d, hd, hd'⟩ := exists_ge_of_prod (A := A) (ϖ := ϖ) (q := a - e / ((T.card - j : ℕ) : ℚ))
    (Q.roots.map ((fun p => eval α p) ∘ fun a => X - C a)) (by
      rw [← Multiset.card_pos, Multiset.card_map, hcard, hQd]; exact hpos)
    (hdiv.mono (le_of_eq (by
      rw [Multiset.card_map, Multiset.card_map, hcard, hQd, Finset.card_val]
      have : ((T.card - j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [← Nat.cast_sub hj.le]
      field_simp)))
  obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hd
  exact ⟨β, hβ, by simpa using hd'⟩

end Step

section Orbit

variable {K : Type} [Field K] [Algebra ℚ K] {A : ValuationSubring K}

def loss (p n : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p n)

theorem loss_mono {p n n' : ℕ} (hp : p.Prime) (h : n ≤ n') : loss p n ≤ loss p n' := by
  have h1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_le
  unfold loss
  gcongr

theorem loss_nonneg {p : ℕ} (hp : p.Prime) (n : ℕ) : 0 ≤ loss p n := by
  have := loss_mono hp (Nat.zero_le n)
  simpa [loss] using this

theorem loss_le_one {p : ℕ} (hp : 3 ≤ p) (n : ℕ) : loss p n ≤ 1 := by
  have h1 : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have h2 : (p : ℚ) / ((p : ℚ) - 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by nlinarith)]; nlinarith
  have h3 : (0 : ℚ) ≤ 1 / (p : ℚ) ^ Nat.log p n := by positivity
  have h4 : (0 : ℚ) ≤ (p : ℚ) / ((p : ℚ) - 1) ^ 2 := by positivity
  unfold loss
  nlinarith [mul_nonneg h3 h4]

theorem valuation_natCast_ge {p : ℕ} (hp : p.Prime) (h1 : A.valuation (p : K) < 1) {c e : ℕ} (hc : ¬ p ^ (e + 1) ∣ c) :
    A.valuation (p : K) ^ e ≤ A.valuation (c : K) := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
  obtain ⟨k, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 p hp.one_lt.ne'
  have hk : k ≤ e := by
    by_contra hk
    exact hc ((pow_dvd_pow p (by omega)).mul_right u)
  have hint : ∀ z : ℤ, A.valuation (z : K) ≤ 1 := fun z => (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have hu1 : 1 ≤ A.valuation (u : K) := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨s, t, hst⟩ : IsCoprime (p : ℤ) (u : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu)
    have e1 : (s : K) * p + t * u = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hst
    have : A.valuation ((s : K) * p + t * u) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint s)) h1
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint t)) hlt
    rw [e1, map_one] at this
    exact lt_irrefl _ this
  rw [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
  exact (pow_le_pow_right_of_le_one' h1.le hk).trans (le_mul_of_one_le_right' hu1)

theorem exists_fixed [IsAlgClosed K] {p : ℕ} (hp : p.Prime) (h1 : A.valuation (p : K) < 1) (H : Subgroup (K ≃ₐ[ℚ] K))
    (hH : ∀ h ∈ H, ∀ x ∈ A, h x ∈ A) (n : ℕ) :
    ∀ (α : K) (a : ℚ) (S : Finset K), S.card ≤ n → (∀ h ∈ H, h α ∈ S) → (∀ h ∈ H, Ge A (p : K) (h α - α) a) →
      ∃ y, (∀ h ∈ H, h y = y) ∧ Ge A (p : K) (α - y) (a - loss p n) := by
  classical
  haveI : CharZero K := algebraRat.charZero K
  have h0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α a S hS hαS hα
  set T := S.filter fun t => ∃ h ∈ H, h α = t with hT
  have hmem : ∀ t, t ∈ T ↔ ∃ h ∈ H, h α = t := fun t => by
    rw [hT, Finset.mem_filter]
    exact ⟨fun h => h.2, fun ⟨h, hh, e⟩ => ⟨e ▸ hαS h hh, h, hh, e⟩⟩
  have hTn : T.card ≤ n := (Finset.card_filter_le _ _).trans hS
  by_cases h2 : 2 ≤ T.card
  swap
  · refine ⟨α, fun h hh => ?_, by simpa using ge_zero _⟩
    exact Finset.card_le_one.mp (by omega : T.card ≤ 1) _ ((hmem _).mpr ⟨h, hh, rfl⟩) _ ((hmem _).mpr ⟨1, H.one_mem, rfl⟩)
  obtain ⟨j, e, hj0, hj, hdvd, hloss⟩ := GlobalTheory.T.exists_choose_small_padicVal_ax_induction p hp T.card h2
  change _ + loss p _ ≤ loss p _ at hloss
  obtain ⟨β, hβ, hαβ⟩ := exists_root_hasseDeriv h0 h1.le T α (a := a) (fun t ht => by
    obtain ⟨h, hh, rfl⟩ := (hmem t).mp ht
    exact (hα h hh).symm) hj (valuation_natCast_ge hp h1 hdvd)
  set P : K[X] := ∏ t ∈ T, (X - C t) with hP
  have hPd : P.natDegree = T.card := by simp [hP]
  have hQd : (hasseDeriv j P).natDegree = T.card - j := by rw [natDegree_hasseDeriv, hPd]
  have hPmap : ∀ h ∈ H, P.map (h : K →+* K) = P := by
    intro h hh
    rw [hP, Polynomial.map_prod]
    refine Finset.prod_bij (fun t _ => h t) (fun t ht => ?_) (fun t _ t' _ e => h.injective e) (fun t ht => ?_) (fun t _ => by simp)
    · obtain ⟨g, hg, rfl⟩ := (hmem t).mp ht
      exact (hmem _).mpr ⟨h * g, H.mul_mem hh hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := (hmem t).mp ht
      exact ⟨(h⁻¹ * g) α, (hmem _).mpr ⟨_, H.mul_mem (H.inv_mem hh) hg, rfl⟩, by
        rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]⟩
  have hQmap : ∀ h ∈ H, (hasseDeriv j P).map (h : K →+* K) = hasseDeriv j P := by
    intro h hh
    ext k
    rw [coeff_map, hasseDeriv_coeff, map_mul, map_natCast, ← coeff_map, hPmap h hh]
  have he : (0 : ℚ) ≤ e / ((T.card - j : ℕ) : ℚ) := by positivity
  obtain ⟨y, hy, hβy⟩ := ih (T.card - j) (by omega) β (a - e / ((T.card - j : ℕ) : ℚ)) (hasseDeriv j P).roots.toFinset
    ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans hQd.le)) (fun h hh => by
      rw [Multiset.mem_toFinset, mem_roots'] at *
      refine ⟨hβ.1, ?_⟩
      rw [← hQmap h hh]
      exact hβ.2.map) (fun h hh => by
      have k1 := hαβ.symm.map h0 (h : K →+* K) (hH h hh) (map_natCast _ p)
      rw [map_sub] at k1
      exact Ge.trans k1 (((hα h hh).mono (by linarith)).trans hαβ))
  have hm := loss_mono hp hTn
  have hnn := loss_nonneg hp (T.card - j)
  exact ⟨y, hy, (hαβ.mono (by linarith)).trans (hβy.mono (by linarith))⟩

end Orbit

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Ord2 in

theorem exists_fixed_congr (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (H : Subgroup (G ℚ Ω)) (hH : H ≤ Dec (F := ℚ) A) (m : ℕ) (x : Ω) (hx : x ∈ A)
    (hcg : ∀ h ∈ H, GlobalTheory.Glue.CgA A l (m + 1) (h x) x) :
    ∃ y ∈ A, (∀ h ∈ H, h y = y) ∧ GlobalTheory.Glue.CgA A l m x y := by
  classical
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have h0 : (l : Ω) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨v, hv, hlv⟩ := hA
  have h1 : A.valuation (l : Ω) < 1 := by simpa using (hv _).mpr hlv
  have hint : IsIntegral ℚ x := (IsAlgClosure.isAlgebraic.isAlgebraic x).isIntegral
  have h3 : 3 ≤ l := by have := hp.two_le; omega
  obtain ⟨y, hy, hxy⟩ := exists_fixed hp h1 H (fun h hh z hz => (apply_mem_iff_of_mem_Dec (hH hh) z).mpr hz) _ x ((m + 1 : ℕ) : ℚ)
    ((minpoly ℚ x).aroots Ω).toFinset le_rfl (fun h _ => by
      rw [Multiset.mem_toFinset, mem_aroots]
      refine ⟨minpoly.ne_zero hint, ?_⟩
      rw [aeval_algHom_apply, minpoly.aeval, map_zero])
    (fun h hh => (ge_natCast_iff h0 h1.le).mpr (hcg h hh))
  have hm : Ge A (l : Ω) (x - y) (m : ℚ) := hxy.mono (by
    have := loss_le_one h3 ((minpoly ℚ x).aroots Ω).toFinset.card
    push_cast; linarith)
  obtain ⟨z, hz, e⟩ := (ge_natCast_iff h0 h1.le).mp hm
  refine ⟨y, ?_, hy, z, hz, e⟩
  have : y = x - (l : Ω) ^ m * z := by rw [← e]; ring
  rw [this]
  exact A.sub_mem hx (A.mul_mem _ _ (A.pow_mem (natCast_mem A l) m) hz)

end GlobalTheory.AxSen
