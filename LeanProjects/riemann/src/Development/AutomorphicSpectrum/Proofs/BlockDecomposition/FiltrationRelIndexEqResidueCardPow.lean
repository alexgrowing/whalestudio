import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureCballZpow

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical

namespace GlobalTheory.CompanionTheory.IwJac.StepIdx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem val_lt_one {ϖ : kˣ} (h : ord k ϖ = 1) : valuation k (ϖ : k) < 1 := by
  have h1 : ¬ valuation k ((1 : kˣ) : k) ≤ valuation k (ϖ : k) := by
    rw [GlobalTheory.OrdShellInt.val_le_iff_ord, ord_eq_zero (x := (1 : kˣ)) (by simp)]; omega
  simpa using h1

theorem val_le_of_lt_one {ϖ : kˣ} (h : ord k ϖ = 1) {y : k} (hy : valuation k y < 1) :
    valuation k y ≤ valuation k (ϖ : k) := by
  by_cases h0 : y = 0
  · subst h0; simp
  have h1 : ¬ valuation k ((1 : kˣ) : k) ≤ valuation k ((Units.mk0 y h0 : kˣ) : k) := by
    simpa using hy
  rw [GlobalTheory.OrdShellInt.val_le_iff_ord, ord_eq_zero (x := (1 : kˣ)) (by simp)] at h1
  have h2 := (GlobalTheory.OrdShellInt.val_le_iff_ord (Units.mk0 y h0) ϖ).2 (by omega)
  simpa using h2

def om (ϖ : kˣ) (h : ord k ϖ = 1) : 𝒪[k] := ⟨ϖ, (val_lt_one h).le⟩

theorem om_pow_dvd_iff {ϖ : kˣ} (h : ord k ϖ = 1) (a : 𝒪[k]) (m : ℕ) :
    om ϖ h ^ m ∣ a ↔ valuation k (a : k) ≤ valuation k ((ϖ : k) ^ m) := by
  refine ((Valuation.integer.integers (valuation k)).dvd_iff_le).trans ?_
  simp only [map_pow]
  rfl

theorem maximalIdeal_eq {ϖ : kˣ} (h : ord k ϖ = 1) :
    IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {om ϖ h} := by
  ext a
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one, Ideal.mem_span_singleton]
  have h1 := om_pow_dvd_iff h a 1
  rw [pow_one, pow_one] at h1
  rw [h1]
  constructor
  · intro ha
    exact val_le_of_lt_one h (lt_of_le_of_ne a.2 ha)
  · intro ha
    exact (lt_of_le_of_lt ha (val_lt_one h)).ne

theorem card_quot {ϖ : kˣ} (h : ord k ϖ = 1) (m : ℕ) :
    Nat.card (𝒪[k] ⧸ Ideal.span {om ϖ h ^ m}) = Nat.card 𝓀[k] ^ m := by
  rw [← Ideal.span_singleton_pow, ← maximalIdeal_eq h]
  have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[k]) (IsDiscreteValuationRing.not_a_field _) (i := m)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  exact hq

def ent (g : GL (Fin n) k) (i j : Fin n) : 𝒪[k] :=
  if h : valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 then ⟨_, h⟩ else 0

theorem nO_int {g : GL (Fin n) k} (hg : g ∈ nO k n) (i j : Fin n) :
    valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  obtain ⟨⟨h, rfl⟩, -⟩ := mem_iwahori.1 hg.1
  exact ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j).2

theorem ent_coe {g : GL (Fin n) k} (hg : g ∈ nO k n) (i j : Fin n) :
    (ent g i j : k) = (g : Matrix (Fin n) (Fin n) k) i j := by
  simp [ent, nO_int hg]

theorem mul_entry {ϖ : kˣ} {x : Fin n → ℤ} {d : ℕ} {g h : GL (Fin n) k} (hg : g ∈ filt ϖ x d)
    (hh : h ∈ filt ϖ x d) {i j : Fin n} (hij : j.val = i.val + (d + 1)) :
    valuation k (((g * h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - (g : Matrix (Fin n) (Fin n) k) i j
        - (h : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k (((ϖ ^ (x i - x j) : kˣ)) : k) := by
  obtain ⟨hgO, dg, -⟩ := mem_filt.1 hg
  obtain ⟨hhO, dh, -⟩ := mem_filt.1 hh
  obtain ⟨g0, g1⟩ := (mem_unipB k).1 hgO.2
  obtain ⟨h0, h1⟩ := (mem_unipB k).1 hhO.2
  have hne : i ≠ j := by intro e; rw [e] at hij; omega
  have e : ((g * h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - (g : Matrix (Fin n) (Fin n) k) i j
        - (h : Matrix (Fin n) (Fin n) k) i j =
      ∑ l, ((g : Matrix (Fin n) (Fin n) k) i l * (h : Matrix (Fin n) (Fin n) k) l j
        - (if l = j then (g : Matrix (Fin n) (Fin n) k) i j else 0)
        - (if l = i then (h : Matrix (Fin n) (Fin n) k) i j else 0)) := by
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp
  rw [e]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rcases lt_trichotomy l i with hl | rfl | hl
  · have a1 : l ≠ i := hl.ne
    have a2 : l ≠ j := by intro e; rw [e] at hl; have := Fin.lt_def.1 hl; omega
    rw [g0 i l hl, if_neg a1, if_neg a2]; simp
  · rw [g1, if_pos rfl, if_neg hne]; simp
  rcases lt_trichotomy l j with hl' | rfl | hl'
  · rw [if_neg hl.ne', if_neg hl'.ne, sub_zero, sub_zero, map_mul]
    have e : (((ϖ ^ (x i - x j) : kˣ)) : k) = ((ϖ ^ (x i - x l) : kˣ) : k) * ((ϖ ^ (x l - x j) : kˣ) : k) := by
      rw [← Units.val_mul, ← _root_.zpow_add]; congr 2; ring
    rw [e, map_mul]
    exact mul_le_mul' (dg _ _ hl (by have := Fin.lt_def.1 hl'; omega))
      (dh _ _ hl' (by have := Fin.lt_def.1 hl; omega))
  · rw [h1, if_pos rfl, if_neg hl.ne']; simp
  · have a2 : l ≠ j := hl'.ne'
    rw [h0 l j hl', if_neg hl.ne', if_neg a2]; simp

def tr0 (c : 𝒪[k]) (i j : Fin n) (hij : i ≠ j) : GL (Fin n) 𝒪[k] :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same _ _ hij]; simp,
    by rw [transvection_mul_transvection_same _ _ hij]; simp⟩

def trv (c : 𝒪[k]) (i j : Fin n) (hij : i ≠ j) : GL (Fin n) k :=
  GeneralLinearGroup.map (algebraMap 𝒪[k] k) (tr0 c i j hij)

theorem trv_apply (c : 𝒪[k]) (i j : Fin n) (hij : i ≠ j) (a b : Fin n) :
    (trv c i j hij : Matrix (Fin n) (Fin n) k) a b =
      (1 : Matrix (Fin n) (Fin n) k) a b + if a = i ∧ b = j then (c : k) else 0 := by
  show algebraMap 𝒪[k] k ((transvection i j c : Matrix (Fin n) (Fin n) 𝒪[k]) a b) = _
  simp only [transvection, Matrix.add_apply, Matrix.single_apply, map_add, Matrix.one_apply]
  congr 1
  · split_ifs <;> simp
  · by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
      rfl
    · rw [if_neg h, if_neg fun e => h ⟨e.1.symm, e.2.symm⟩, map_zero]

theorem trv_inv (c : 𝒪[k]) (i j : Fin n) (hij : i ≠ j) : (trv c i j hij)⁻¹ = trv (-c) i j hij := by
  have e : (tr0 c i j hij)⁻¹ = tr0 (-c) i j hij := Units.ext rfl
  rw [trv, ← map_inv, e]
  rfl

theorem trv_nO (c : 𝒪[k]) {i j : Fin n} (hij : i < j) : trv c i j hij.ne ∈ nO k n := by
  have low : ∀ a b : Fin n, b < a → (trv c i j hij.ne : Matrix (Fin n) (Fin n) k) a b = 0 := by
    intro a b hab
    rw [trv_apply, Matrix.one_apply_ne hab.ne', if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact absurd hij (not_lt.2 hab.le)
  refine ⟨mem_iwahori.2 ⟨⟨tr0 c i j hij.ne, rfl⟩, fun a b hab => ?_⟩, (mem_unipB k).2 ⟨low, fun a => ?_⟩⟩
  · rw [low a b hab]; simp
  · rw [trv_apply, Matrix.one_apply_eq, if_neg, add_zero]
    rintro ⟨rfl, h⟩
    exact hij.ne h

theorem trv_deep (ϖ : kˣ) (x : Fin n → ℤ) {d : ℕ} (c : 𝒪[k]) {i j : Fin n} (hij : i ≠ j)
    (hd : j.val = i.val + (d + 1)) : Deep ϖ x d (trv c i j hij) := by
  intro a b hab hb
  rw [trv_apply, Matrix.one_apply_ne hab.ne, if_neg, add_zero, map_zero]
  · exact zero_le'
  · rintro ⟨rfl, rfl⟩
    omega

theorem trv_filt (ϖ : kˣ) (x : Fin n → ℤ) {d : ℕ} (c : 𝒪[k]) {i j : Fin n} (hij : i < j)
    (hd : j.val = i.val + (d + 1)) : trv c i j hij.ne ∈ filt ϖ x d :=
  mem_filt.2 ⟨trv_nO c hij, trv_deep ϖ x c hij.ne hd, by rw [trv_inv]; exact trv_deep ϖ x _ hij.ne hd⟩

theorem coe_zpow_eq {ϖ : kˣ} {e : ℤ} (he : 0 ≤ e) : (((ϖ ^ e : kˣ)) : k) = (ϖ : k) ^ e.toNat := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le he
  simp

theorem mem_span_iff {ϖ : kˣ} (h : ord k ϖ = 1) (a : 𝒪[k]) {e : ℤ} (he : 0 ≤ e) :
    a ∈ Ideal.span {om ϖ h ^ e.toNat} ↔ valuation k (a : k) ≤ valuation k (((ϖ ^ e : kˣ)) : k) := by
  rw [Ideal.mem_span_singleton, om_pow_dvd_iff, coe_zpow_eq he]

abbrev AQ (ϖ : kˣ) (h : ord k ϖ = 1) (x : Fin n → ℤ) (p : Fin n × Fin n) : Type :=
  𝒪[k] ⧸ Ideal.span {om ϖ h ^ (x p.1 - x p.2).toNat}

theorem pair_lt {d : ℕ} (p : diagPairs n d) : p.1.1 < p.1.2 := by
  have := (Finset.mem_filter.1 p.2).2
  exact Fin.lt_def.2 (by omega)

theorem pair_eq {d : ℕ} (p : diagPairs n d) : p.1.2.val = p.1.1.val + (d + 1) :=
  (Finset.mem_filter.1 p.2).2

theorem pair_nonneg {x : Fin n → ℤ} (hx : StrictAnti x) {d : ℕ} (p : diagPairs n d) :
    0 ≤ x p.1.1 - x p.1.2 :=
  sub_nonneg.2 (hx (pair_lt p)).le

def phi {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) :
    filt ϖ x d →* Multiplicative (∀ p : diagPairs n d, AQ ϖ h x p.1) :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd fun p => Ideal.Quotient.mk _ (ent g.1 p.1.1 p.1.2)) fun g g' => by
    rw [← ofAdd_add]
    congr 1
    funext p
    rw [Pi.add_apply, ← map_add, Ideal.Quotient.eq, mem_span_iff h _ (pair_nonneg hx p)]
    have e := mul_entry g.2 g'.2 (pair_eq p)
    have hO : g.1 * g'.1 ∈ nO k n := mul_mem g.2.1 g'.2.1
    have e2 : ((ent (g.1 * g'.1) p.1.1 p.1.2 - (ent g.1 p.1.1 p.1.2 + ent g'.1 p.1.1 p.1.2) : 𝒪[k]) : k) =
        ((g.1 * g'.1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p.1.1 p.1.2
          - (g.1 : Matrix (Fin n) (Fin n) k) p.1.1 p.1.2 - (g'.1 : Matrix (Fin n) (Fin n) k) p.1.1 p.1.2 := by
      show (ent (g.1 * g'.1) p.1.1 p.1.2 : k) - ((ent g.1 p.1.1 p.1.2 : k) + (ent g'.1 p.1.1 p.1.2 : k)) = _
      rw [ent_coe hO, ent_coe g.2.1, ent_coe g'.2.1]
      ring
    show valuation k ((ent (g.1 * g'.1) p.1.1 p.1.2 - (ent g.1 p.1.1 p.1.2 + ent g'.1 p.1.1 p.1.2) : 𝒪[k]) : k) ≤ _
    rw [e2]
    exact e

theorem phi_apply {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) (g : filt ϖ x d) :
    phi h hx d g = Multiplicative.ofAdd fun p => Ideal.Quotient.mk _ (ent g.1 p.1.1 p.1.2) := rfl

theorem phi_eq_one_iff {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) (g : filt ϖ x d) :
    phi h hx d g = 1 ↔ ∀ p : diagPairs n d, valuation k ((g.1 : Matrix (Fin n) (Fin n) k) p.1.1 p.1.2) ≤
      valuation k (((ϖ ^ (x p.1.1 - x p.1.2) : kˣ)) : k) := by
  rw [phi_apply, ← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq, funext_iff]
  refine forall_congr' fun p => ?_
  rw [Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, mem_span_iff h _ (pair_nonneg hx p), ent_coe g.2.1]

theorem deep_succ {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {d : ℕ} (g : filt ϖ x d)
    (hg : phi h hx d g = 1) : Deep ϖ x (d + 1) g.1 := by
  intro i j hij hj
  by_cases hd : j.val ≤ i.val + d
  · exact g.2.2.1 i j hij hd
  · have hm : (i, j) ∈ diagPairs n d := Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp only; omega⟩
    exact (phi_eq_one_iff h hx d g).1 hg ⟨_, hm⟩

theorem ker_phi {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) :
    (phi h hx d).ker = (filt ϖ x (d + 1)).subgroupOf (filt ϖ x d) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    have hi : phi h hx d g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
    exact mem_filt.2 ⟨g.2.1, deep_succ h hx g hg, deep_succ h hx g⁻¹ hi⟩
  · intro hg
    refine (phi_eq_one_iff h hx d g).2 fun p => ?_
    exact (mem_filt.1 hg).2.1 _ _ (pair_lt p) (by have := pair_eq p; omega)

theorem phi_trv {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) (p : diagPairs n d)
    (c : 𝒪[k]) :
    phi h hx d ⟨trv c p.1.1 p.1.2 (pair_lt p).ne, trv_filt ϖ x c (pair_lt p) (pair_eq p)⟩ =
      Multiplicative.ofAdd (Pi.single p (Ideal.Quotient.mk _ c)) := by
  rw [phi_apply]
  congr 1
  funext p'
  have hO := trv_nO c (pair_lt p)
  by_cases e : p' = p
  · subst e
    rw [Pi.single_eq_same]
    congr 1
    refine Subtype.ext ((ent_coe hO _ _).trans ?_)
    rw [trv_apply, Matrix.one_apply_ne (pair_lt p').ne, if_pos ⟨rfl, rfl⟩, zero_add]
  · rw [Pi.single_eq_of_ne e]
    have : ent (trv c p.1.1 p.1.2 (pair_lt p).ne) p'.1.1 p'.1.2 = 0 := by
      refine Subtype.ext ((ent_coe hO _ _).trans ?_)
      rw [trv_apply, Matrix.one_apply_ne (pair_lt p').ne, if_neg, add_zero]
      · rfl
      · rintro ⟨e1, e2⟩
        exact e (Subtype.ext (Prod.ext e1 e2))
    simp only [this, map_zero]

theorem phi_surjective {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) :
    Function.Surjective (phi h hx d) := by
  intro f
  have key : f ∈ (phi h hx d).range := by
    have e : f = ∏ p, Multiplicative.ofAdd (Pi.single p (Multiplicative.toAdd f p) :
        ∀ p : diagPairs n d, AQ ϖ h x p.1) := by
      rw [← ofAdd_sum, Finset.univ_sum_single]
      rfl
    rw [e]
    refine Subgroup.prod_mem _ fun p _ => ?_
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (Multiplicative.toAdd f p)
    exact ⟨_, (phi_trv h hx d p c).trans (by rw [hc])⟩
  exact key

end GlobalTheory.CompanionTheory.IwJac.StepIdx

namespace GlobalTheory.CompanionTheory.IwJac

theorem relIndex_filt_succ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x → ∀ d : ℕ, (filt ϖ x (d + 1)).relIndex (filt ϖ x d) = Nat.card 𝓀[k] ^ ∑ p ∈ diagPairs n d, (x p.1 - x p.2).toNat := by
  intro k _ _ _ _ n ϖ h x hx d
  rw [Subgroup.relIndex, ← StepIdx.ker_phi h hx d, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (StepIdx.phi_surjective h hx d), Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp only [StepIdx.card_quot h]
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_coe_sort (diagPairs n d) fun p => (x p.1 - x p.2).toNat]

end GlobalTheory.CompanionTheory.IwJac

end
