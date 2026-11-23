import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDelta

open scoped Pointwise

section General

variable {Ω : Type} [Field Ω] (A : ValuationSubring Ω)

theorem val_le_one_of_sub_one {b : Ω} (h : A.valuation (b - 1) < 1) : A.valuation b ≤ 1 := by
  have e : b = (b - 1) + 1 := by ring
  rw [e]
  exact Valuation.map_add_le _ h.le (by rw [map_one])

theorem val_mul_lt_one_left {x y : Ω} (hx : A.valuation x < 1) (hy : A.valuation y ≤ 1) :
    A.valuation (x * y) < 1 := by
  rw [map_mul]
  calc A.valuation x * A.valuation y ≤ A.valuation x * 1 := by gcongr
    _ = A.valuation x := mul_one _
    _ < 1 := hx

theorem iter_lt_one (τ : Ω ≃+* Ω) (hm : ∀ x, A.valuation (τ x) < 1 ↔ A.valuation x < 1) (k : ℕ) (x : Ω) :
    A.valuation (τ^[k] x) < 1 ↔ A.valuation x < 1 := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, hm]

theorem iter_div (τ : Ω ≃+* Ω) (k : ℕ) (x y : Ω) : τ^[k] (x / y) = τ^[k] x / τ^[k] y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      map_div₀, ih]

theorem iter_ne_zero (τ : Ω ≃+* Ω) (k : ℕ) {y : Ω} (hy : y ≠ 0) : τ^[k] y ≠ 0 := by
  induction k generalizing y with
  | zero => exact hy
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (by simpa using hy)

theorem prod_iter_div (τ : Ω ≃+* Ω) {y : Ω} (hy : y ≠ 0) (k : ℕ) :
    ∏ i ∈ Finset.range k, τ^[i] (τ y / y) = τ^[k] y / y := by
  induction k with
  | zero => simp [div_self hy]
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, iter_div, ← Function.iterate_succ_apply, Function.iterate_succ_apply' τ k y]
    have h1 := iter_ne_zero τ k hy
    field_simp

theorem prod_lt_one (τ : Ω ≃+* Ω) (hm : ∀ x, A.valuation (τ x) < 1 ↔ A.valuation x < 1) {b : Ω}
    (hb : A.valuation b < 1) (k : ℕ) : A.valuation (∏ i ∈ Finset.range (k + 1), τ^[i] b) < 1 := by
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    rw [Finset.prod_range_succ]
    exact val_mul_lt_one_left A ih ((iter_lt_one A τ hm _ b).2 hb).le

theorem val_div_eq_one (τ : Ω ≃+* Ω) (hm : ∀ x, A.valuation (τ x) < 1 ↔ A.valuation x < 1) {y : Ω} (hy : y ≠ 0)
    {n : ℕ} (hn : 0 < n) (h : τ^[n] y = y) : A.valuation (τ y / y) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hP : ∏ i ∈ Finset.range (k + 1), τ^[i] (τ y / y) = 1 := by
    rw [prod_iter_div τ hy, h, div_self hy]
  have hy' : τ y ≠ 0 := by simpa using hy
  have ha : τ y / y ≠ 0 := div_ne_zero hy' hy
  have h1 : ¬ A.valuation (τ y / y) < 1 := fun hlt => by
    have := prod_lt_one A τ hm hlt k
    rw [hP, map_one] at this
    exact lt_irrefl _ this
  have h2 : ¬ A.valuation (τ y / y)⁻¹ < 1 := fun hlt => by
    have := prod_lt_one A τ hm hlt k
    have e : ∏ i ∈ Finset.range (k + 1), τ^[i] (τ y / y)⁻¹ = 1 := by
      have : ∀ i, τ^[i] (τ y / y)⁻¹ = (τ^[i] (τ y / y))⁻¹ := fun i => by
        rw [inv_eq_one_div, iter_div, inv_eq_one_div]
        congr 1
        induction i with
        | zero => rfl
        | succ i ih => rw [Function.iterate_succ_apply, map_one, ih]
      simp only [this, Finset.prod_inv_distrib, hP, inv_one]
    rw [e, map_one] at this
    exact lt_irrefl _ this
  rw [map_inv₀] at h2
  have h0 : A.valuation (τ y / y) ≠ 0 := by simpa using ha
  push_neg at h1 h2
  exact le_antisymm ((one_le_inv₀ (zero_lt_iff.2 h0)).1 h2) h1

end General

end GlobalTheory.SplitDelta

namespace GlobalTheory.SplitDelta

section General2

variable {Ω : Type} [Field Ω] (A : ValuationSubring Ω)

theorem val_sub_one_mul {b c : Ω} (hb : A.valuation (b - 1) < 1) (hc : A.valuation (c - 1) < 1) :
    A.valuation (b * c - 1) < 1 := by
  have e : b * c - 1 = (b - 1) * c + (c - 1) := by ring
  rw [e]
  exact Valuation.map_add_lt _ (val_mul_lt_one_left A hb (val_le_one_of_sub_one A hc)) hc

theorem fixes_of_wild (s : Ω ≃+* Ω) (hm : ∀ x, A.valuation (s x) < 1 ↔ A.valuation x < 1) (S : Subfield Ω)
    (hS : ∀ y ∈ S, s y ∈ S) (h3 : ∀ y ∈ S, s (s (s y)) = y) (h3u : ¬ A.valuation (3 : Ω) < 1)
    (H : ∀ y ∈ S, y ≠ 0 → A.valuation (s y / y - 1) < 1) : ∀ z ∈ S, s z = z := by
  intro z hz
  by_cases hz0 : z = 0
  · rw [hz0, map_zero]
  by_contra hne
  set u := s z / z - 1 with hu_def
  have hu0 : u ≠ 0 := fun h => hne (by
    rw [hu_def, sub_eq_zero, div_eq_one_iff_eq hz0] at h; exact h)
  have huS : u ∈ S := S.sub_mem (S.div_mem (hS z hz) hz) S.one_mem
  have hu : A.valuation u < 1 := H z hz hz0
  set b1 := s u / u with hb1_def
  have hb1 : A.valuation (b1 - 1) < 1 := H u huS hu0
  have hsb1 : A.valuation (s b1 - 1) < 1 := by
    rw [← map_one s, ← map_sub, hm]; exact hb1
  have hb2 : A.valuation (s b1 * b1 - 1) < 1 := val_sub_one_mul A hsb1 hb1
  have e1 : s z = z * (1 + u) := by rw [hu_def]; field_simp; ring
  have e2 : s u = u * b1 := by rw [hb1_def]; field_simp
  have e3 : s (s (s z)) = z * ((1 + u) * (1 + u * b1) * (1 + u * (s b1 * b1))) := by
    simp only [e1, map_mul, map_add, map_one, e2]
    ring
  have hX : (1 + u) * (1 + u * b1) * (1 + u * (s b1 * b1)) = 1 := by
    have := (h3 z hz).symm.trans e3
    exact (mul_left_cancel₀ hz0 (by rw [mul_one]; exact this.symm))
  set b2 := s b1 * b1 with hb2_def
  have hY : 1 + b1 + b2 + u * (b1 + b2 + b1 * b2) + u ^ 2 * (b1 * b2) = 0 := by
    have : u * (1 + b1 + b2 + u * (b1 + b2 + b1 * b2) + u ^ 2 * (b1 * b2)) = 0 := by
      linear_combination hX
    exact (mul_eq_zero.1 this).resolve_left hu0
  have e4 : (3 : Ω) = -((b1 - 1) + (b2 - 1) + u * (b1 + b2 + b1 * b2 + u * (b1 * b2))) := by
    linear_combination hY
  apply h3u
  rw [e4, Valuation.map_neg]
  have l1 := val_le_one_of_sub_one A hb1
  have l2 := val_le_one_of_sub_one A hb2
  have l12 : A.valuation (b1 * b2) ≤ 1 := by rw [map_mul]; exact mul_le_one' l1 l2
  have lY : A.valuation (b1 + b2 + b1 * b2 + u * (b1 * b2)) ≤ 1 :=
    Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ l1 l2) l12)
      (val_mul_lt_one_left A hu l12).le
  exact Valuation.map_add_lt _ (Valuation.map_add_lt _ hb1 hb2) (val_mul_lt_one_left A hu lY)

theorem exists_cube_root_mod {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) : ∃ t : ℕ, p ∣ t ^ 2 + t + 1 := by
  haveI := Fact.mk hp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]; omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hcard
  have h3 : (u : ZMod p) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have h1 : (u : ZMod p) ≠ 1 := fun h => by
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu; norm_num at hu
  have h2 : (u : ZMod p) ^ 2 + u + 1 = 0 := by
    have : ((u : ZMod p) - 1) * ((u : ZMod p) ^ 2 + u + 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)
  refine ⟨(u : ZMod p).val, (ZMod.natCast_eq_zero_iff _ _).1 ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact h2

theorem fix_cube_root (τ : Ω ≃+* Ω) (hm : ∀ x, A.valuation (τ x) < 1 ↔ A.valuation x < 1) {p : ℕ} (hp : p.Prime)
    (hp3 : p % 3 = 1) (hpv : A.valuation (p : Ω) < 1) {a : Ω} (ha : A.valuation a ≤ 1)
    (ha3 : A.valuation (a ^ 3 - 1) < 1) : A.valuation (τ a - a) < 1 := by
  obtain ⟨t, k, hk⟩ := exists_cube_root_mod hp hp3
  have hk' : (t : Ω) ^ 2 + t + 1 = p * k := by
    have := congrArg (Nat.cast : ℕ → Ω) hk; push_cast at this; exact this
  have hnat : ∀ s : ℕ, A.valuation (a - s) < 1 → A.valuation (τ a - a) < 1 := fun s hs => by
    have e : τ a - a = τ (a - s) - (a - s) := by rw [map_sub, map_natCast]; ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ((hm _).2 hs) hs)
  have hs1 : ∀ s : ℕ, A.valuation (s : Ω) ≤ 1 := fun s => (A.valuation_le_one_iff _).2 (natCast_mem A s)
  have hle : ∀ s : ℕ, A.valuation (a - s) ≤ 1 := fun s =>
    le_trans (Valuation.map_sub _ _ _) (max_le ha (hs1 s))
  have key : (a - 1) * (a - t) * (a - ((t ^ 2 : ℕ) : Ω)) = (a ^ 3 - 1) - p * k * (a - 1) * ((a - t) + 1) := by
    push_cast
    first
    | linear_combination (-(a - 1) * (a - t + 1)) * hk'
    | linear_combination ((a - 1) * (a - t + 1)) * hk'
  have hR : A.valuation ((a ^ 3 - 1) - p * k * (a - 1) * ((a - t) + 1)) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha3 ?_)
    refine val_mul_lt_one_left A (val_mul_lt_one_left A (val_mul_lt_one_left A hpv (hs1 k)) (by simpa using hle 1))
      (Valuation.map_add_le _ (hle t) (by rw [map_one]))
  rw [← key] at hR
  by_contra hno
  have n1 : ¬ A.valuation (a - ((1 : ℕ) : Ω)) < 1 := fun h => hno (hnat 1 h)
  have n2 : ¬ A.valuation (a - t) < 1 := fun h => hno (hnat t h)
  have n3 : ¬ A.valuation (a - ((t ^ 2 : ℕ) : Ω)) < 1 := fun h => hno (hnat _ h)
  push_neg at n1 n2 n3
  rw [Nat.cast_one] at n1
  rw [map_mul, map_mul] at hR
  exact absurd hR (not_lt.2 (one_le_mul (one_le_mul n1 n2) n3))

end General2

end GlobalTheory.SplitDelta

namespace GlobalTheory.SplitDelta

theorem exists_iterate_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] (τ : Ω ≃+* Ω) {y : Ω} (hy : IsIntegral ℚ y) :
    ∃ n, 0 < n ∧ τ^[n] y = y := by
  set f := minpoly ℚ y
  have hf : f ≠ 0 := minpoly.ne_zero hy
  have hroot : ∀ k, τ^[k] y ∈ f.rootSet Ω := by
    intro k
    induction k with
    | zero => exact (Polynomial.mem_rootSet.2 ⟨hf, minpoly.aeval ℚ y⟩)
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [Polynomial.mem_rootSet] at ih ⊢
      refine ⟨hf, ?_⟩
      have := Polynomial.aeval_algHom_apply (τ : Ω →+* Ω).toRatAlgHom (τ^[k] y) f
      rw [ih.2, map_zero] at this
      exact this
  haveI := (Polynomial.rootSet_finite f Ω).to_subtype
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨τ^[k] y, hroot k⟩ : f.rootSet Ω))
  have he' : τ^[i] y = τ^[j] y := congrArg Subtype.val he
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨j - i, by omega, τ.injective.iterate i ?_⟩
    rw [← Function.iterate_add_apply, show i + (j - i) = j by omega, he']
  · refine ⟨i - j, by omega, τ.injective.iterate j ?_⟩
    rw [← Function.iterate_add_apply, show j + (i - j) = i by omega, he']

end GlobalTheory.SplitDelta

namespace GlobalTheory.SplitDelta

open GlobalTheory.AntiRamConj

theorem places_split : ∀ (D : D7) (i : D.ntw.Tw), ∀ P ∈ D.ntw.pD i, Formalism.BasicNotions.IsSplitPl D.host P := by
  intro D i P hP
  by_contra hns
  have hcp : IsConjPl D.host P P := by
    intro x y hxy
    constructor
    · intro hx
      by_contra hy
      exact hns ⟨x, hx, fun y' hy' => by
        have : y' = y := Subtype.ext (hy'.trans hxy.symm)
        rw [this]; exact hy⟩
    · intro hy
      by_contra hx
      exact hns ⟨y, hy, fun x' hx' => by
        have : x' = x := Subtype.ext (hx'.trans (by rw [hxy, host_conj_conj]; rfl))
        rw [this]; exact hx⟩
  have hA : IsPlaceOver (D.nd.plOm.1 P) P := D.nd.plOm.2 P
  obtain ⟨p, hp, hp15, hpP⟩ : ∃ p : ℕ, p.Prime ∧ p % 15 = 1 ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h := D.ntw.pD_eq i
    have hm : P ∈ (D.ntw.pD i : Set _) := hP
    rw [h] at hm
    split_ifs at hm
    · exact ⟨_, D.host.pde'_prime, D.host.pde_mod.2, hm⟩
    · exact ⟨_, D.host.pde_prime, D.host.pde_mod.1, hm⟩
  set A := D.nd.plOm.1 P with hA_def
  have hpv : A.valuation (p : D.nd.Om) < 1 := by
    have := (hA (p : 𝓞 D.host.E)).2 hpP
    simpa using this
  have h3u : ¬ A.valuation (3 : D.nd.Om) < 1 := by
    intro h3
    have e : (1 : D.nd.Om) = p - 3 * ((p / 3 : ℕ) : D.nd.Om) := by
      have h' : p = 3 * (p / 3) + 1 := by omega
      have := congrArg (Nat.cast : ℕ → D.nd.Om) h'
      push_cast at this
      linear_combination -this
    have h1 := Valuation.map_sub A.valuation (p : D.nd.Om) (3 * ((p / 3 : ℕ) : D.nd.Om))
    rw [← e, map_one] at h1
    have h2 : A.valuation (3 * ((p / 3 : ℕ) : D.nd.Om)) < 1 :=
      val_mul_lt_one_left A h3 ((A.valuation_le_one_iff _).2 (natCast_mem A _))
    exact absurd (lt_of_le_of_lt h1 (max_lt hpv h2)) (lt_irrefl _)
  have hcard := D.ntw.delta_15 i P hP A hA
  haveI : Finite ((Ine (F := D.host.E) A).map (D.ntw.delta i)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ((Ine (F := D.host.E) A).map (D.ntw.delta i))) 3
    (by rw [hcard]; norm_num)
  obtain ⟨σ, hσ, hσx⟩ := Subgroup.mem_map.1 x.2
  have hord : orderOf (D.ntw.delta i σ) = 3 := by rw [hσx, Subgroup.orderOf_coe]; exact hx
  have hd3 : D.ntw.delta i σ ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hd1 : D.ntw.delta i σ ≠ 1 := fun h => by rw [h, orderOf_one] at hord; norm_num at hord
  haveI : IsGalois D.host.E D.nd.Om := IsAlgClosure.isGalois _ _
  set K := (D.ntw.delta i).ker with hK_def
  have hfix : (IntermediateField.fixedField K).fixingSubgroup = K :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨K, K.isClosed_of_isOpen (D.ntw.delta_open i)⟩
  set L := IntermediateField.fixedField K with hL_def
  have memL : ∀ y, y ∈ L ↔ ∀ k ∈ K, k y = y := fun y => by
    rw [hL_def, IntermediateField.mem_fixedField_iff]
  have hσL : ∀ y ∈ L, σ y ∈ L := fun y hy => (memL _).2 fun k hk => by
    have hk' : σ⁻¹ * k * σ ∈ K := by
      rw [MonoidHom.mem_ker] at hk ⊢
      rw [map_mul, map_mul, hk, mul_one, map_inv, inv_mul_cancel]
    have h1 := (memL y).1 hy _ hk'
    have h2 : σ ((σ⁻¹ * k * σ) y) = σ y := by rw [h1]
    rw [← AlgEquiv.mul_apply, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, AlgEquiv.mul_apply] at h2
    exact h2
  have h3L : ∀ y ∈ L, σ (σ (σ y)) = y := fun y hy => by
    have hk : σ ^ 3 ∈ K := by rw [MonoidHom.mem_ker, map_pow, hd3]
    have := (memL y).1 hy _ hk
    simpa [pow_succ, AlgEquiv.mul_apply] using this
  have hσm : ∀ x, A.valuation (σ x) < 1 ↔ A.valuation x < 1 := valuation_apply_lt_one_iff hσ.1
  obtain ⟨z, hzL, hz0, hza⟩ : ∃ z ∈ L, z ≠ 0 ∧ ¬ A.valuation (σ z / z - 1) < 1 := by
    by_contra hall
    push_neg at hall
    have hfixσ := fixes_of_wild A σ.toRingEquiv hσm L.toSubfield hσL (fun y hy => h3L y hy) h3u
      (fun y hy hy0 => hall y hy hy0)
    have : σ ∈ K := by
      rw [← hfix]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => hfixσ y hy
    exact hd1 this
  have hσz0 : σ z ≠ 0 := by simpa using hz0
  set a := σ z / z with ha_def
  have ha1 : A.valuation a = 1 := val_div_eq_one A σ.toRingEquiv hσm hz0 (n := 3) (by norm_num) (h3L z hzL)
  have hc : ∀ x : D.host.E, ∃ y : D.host.E,
      D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y :=
    fun x => ⟨_, cc_symm_algebraMap_host D x⟩
  set σ' := conjAut D.ntw.cc hc σ with hσ'_def
  have hδ' : D.ntw.delta i σ' = (D.ntw.delta i σ)⁻¹ := D.ntw.delta_anti i σ σ' (conjAut_apply _ hc σ)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (isPlaceOver_moveVal D hcp hA) hA
  let τ : D.nd.Om ≃+* D.nd.Om := D.ntw.cc.trans g.toRingEquiv
  have hτ : ∀ x, τ x = g (D.ntw.cc x) := fun _ => rfl
  have hτA : ∀ x, τ x ∈ A ↔ x ∈ A := fun x => by
    have h1 := (ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := moveVal D.ntw.cc A) (x := D.ntw.cc x))
    rw [hg, AlgEquiv.smul_def] at h1
    rw [hτ, h1, mem_moveVal, RingEquiv.symm_apply_apply]
  have hτm : ∀ x, A.valuation (τ x) < 1 ↔ A.valuation x < 1 := fun x => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', hτA, ← map_inv₀, hτA, map_eq_zero_iff _ τ.injective]
  set w := τ.symm z with hw_def
  have hτw : τ w = z := τ.apply_symm_apply z
  have hw0 : w ≠ 0 := fun h => hz0 (by rw [← hτw, h, map_zero])
  have hρ : τ (σ w) = σ (σ z) := by
    have hk : (σ * σ)⁻¹ * (g * σ' * g⁻¹) ∈ K := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hδ']
      rw [mul_comm (D.ntw.delta i g), mul_inv_cancel_right, ← mul_inv, ← sq, ← pow_succ, hd3, inv_one]
    have h1 := (memL z).1 hzL _ hk
    have h2 : (σ * σ) (((σ * σ)⁻¹ * (g * σ' * g⁻¹)) z) = (σ * σ) z := by rw [h1]
    rw [← AlgEquiv.mul_apply, mul_inv_cancel_left] at h2
    exact h2
  haveI : CharZero D.nd.Om := charZero_of_injective_algebraMap (algebraMap D.host.E D.nd.Om).injective
  have hIntW : IsIntegral ℚ w := by
    haveI : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic ℚ D.nd.Om := Algebra.IsAlgebraic.trans ℚ D.host.E D.nd.Om
    exact (Algebra.IsAlgebraic.isAlgebraic w).isIntegral
  obtain ⟨n, hn, hnw⟩ := exists_iterate_eq τ hIntW
  have hwz : A.valuation (z / w) = 1 := by
    have := val_div_eq_one A τ hτm hw0 hn hnw
    rwa [hτw] at this
  set r := w / z with hr_def
  have hr1 : A.valuation r = 1 := by
    rw [hr_def, ← inv_div, map_inv₀, hwz, inv_one]
  have hr0 : r ≠ 0 := div_ne_zero hw0 hz0
  have hσr : A.valuation (σ r - r) < 1 := hσ.2 r (le_of_eq hr1)
  have hw : w = z * r := by rw [hr_def]; field_simp
  have hba : A.valuation (σ w / w - a) < 1 := by
    have e : σ w / w - a = a * (σ r - r) * r⁻¹ := by
      rw [hw, map_mul, ha_def]; field_simp
    rw [e, map_mul, map_mul, ha1, one_mul, map_inv₀, hr1, inv_one, mul_one]
    exact hσr
  have hτb : τ (σ w / w) = σ a * a := by
    rw [map_div₀, hρ, hτw, ha_def, map_div₀]
    have : σ (σ z) ≠ 0 := by simpa using hσz0
    field_simp
  have hσa : A.valuation (σ a - a) < 1 := hσ.2 a (le_of_eq ha1)
  have hdec1 : ∀ y, A.valuation y ≤ 1 → A.valuation (σ y) ≤ 1 := fun y hy => by
    rw [ValuationSubring.valuation_le_one_iff] at hy ⊢
    exact (apply_mem_iff_of_mem_Dec hσ.1 y).2 hy
  have hσa1 : A.valuation (σ a) ≤ 1 := hdec1 a (le_of_eq ha1)
  have hσσa1 : A.valuation (σ (σ a)) ≤ 1 := hdec1 _ hσa1
  have hσσa : A.valuation (σ (σ a) - σ a) < 1 := hσ.2 _ hσa1
  have hprod : a * σ a * σ (σ a) = 1 := by
    have h3 := h3L z hzL
    rw [ha_def]
    simp only [map_div₀]
    rw [h3]
    have : σ (σ z) ≠ 0 := by simpa using hσz0
    field_simp
  have ha3 : A.valuation (a ^ 3 - 1) < 1 := by
    have e : a ^ 3 - 1 = (a * a) * ((a - σ a) + (σ a - σ (σ a))) + (a * σ (σ a)) * (a - σ a) := by
      linear_combination hprod
    have h1 : A.valuation (a - σ a) < 1 := by rw [Valuation.map_sub_swap]; exact hσa
    have h2 : A.valuation (σ a - σ (σ a)) < 1 := by rw [Valuation.map_sub_swap]; exact hσσa
    have haa : A.valuation (a * a) ≤ 1 := by rw [map_mul, ha1, one_mul]
    have haσ : A.valuation (a * σ (σ a)) ≤ 1 := by rw [map_mul, ha1, one_mul]; exact hσσa1
    rw [e, mul_comm (a * a), mul_comm (a * σ (σ a))]
    exact Valuation.map_add_lt _ (val_mul_lt_one_left A (Valuation.map_add_lt _ h1 h2) haa)
      (val_mul_lt_one_left A h1 haσ)
  have hτa := fix_cube_root A τ hτm hp (by omega) hpv (le_of_eq ha1) ha3
  have hfin : A.valuation (a * (a - 1)) < 1 := by
    have e : a * (a - 1) = -((σ a - a) * a) + τ (σ w / w - a) + (τ a - a) := by
      rw [map_sub, hτb]; ring
    rw [e]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ ((hτm _).2 hba)) hτa
    rw [Valuation.map_neg]
    exact val_mul_lt_one_left A hσa (le_of_eq ha1)
  rw [map_mul, ha1, one_mul] at hfin
  exact hza hfin

end GlobalTheory.SplitDelta
