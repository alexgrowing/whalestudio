import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen

noncomputable section

open ValuativeRel Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

namespace PositivityTheory.ThK.GaussNe

section Generic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rep {c : ℕ} (y : Res k c) : k := ((Quotient.out y : 𝒪[k]) : k)

theorem rep_le_one {c : ℕ} (y : Res k c) : valuation k (rep y) ≤ 1 := by
  exact (Quotient.out y).2

theorem mk_eq_mk_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (a b : 𝒪[k]) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) a = Ideal.Quotient.mk _ b ↔
      valuation k ((a : k) - b) ≤ valuation k (ϖ : k) ^ c := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (Valuation.integer.integers (valuation k)).dvd_iff_le, map_pow, map_pow]
  exact Iff.rfl

theorem val_pow_lt_one {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) : valuation k (ϖ : k) ^ c < 1 := by
  have h1 : valuation k (ϖ : k) < 1 := by
    rw [hϖ]
    first
      | exact ValuativeRel.uniformizer_lt_one k
      | exact ValuativeRel.uniformizer_lt_one
      | exact ValuativeRel.uniformizer_lt_one (R := k)
  exact pow_lt_one₀ zero_le h1 (by omega)

theorem val_rep_unit {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) :
    valuation k (rep (y : Res k c)) = 1 := by
  have hy : Ideal.Quotient.mk _ (Quotient.out (y : Res k c)) = (y : Res k c) := Quotient.out_eq _
  have hz : Ideal.Quotient.mk _ (Quotient.out ((y⁻¹ : (Res k c)ˣ) : Res k c)) = ((y⁻¹ : (Res k c)ˣ) : Res k c) :=
    Quotient.out_eq _
  have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c)
      (Quotient.out (y : Res k c) * Quotient.out ((y⁻¹ : (Res k c)ˣ) : Res k c)) =
      Ideal.Quotient.mk _ 1 := by
    rw [map_mul, hy, hz, Units.mul_inv, map_one]
  have hv := (mk_eq_mk_iff hϖ c _ _).1 hmk
  have hlt : valuation k (((Quotient.out (y : Res k c) * Quotient.out ((y⁻¹ : (Res k c)ˣ) : Res k c) : 𝒪[k]) : k) - 1) < 1 :=
    lt_of_le_of_lt (by simpa using hv) (val_pow_lt_one hϖ hc)
  have hone := Valuation.map_one_add_of_lt (valuation k) hlt
  rw [add_sub_cancel] at hone
  have hb : valuation k (rep ((y⁻¹ : (Res k c)ˣ) : Res k c)) ≤ 1 := rep_le_one _
  refine le_antisymm (rep_le_one _) ?_
  calc (1 : ValueGroupWithZero k) = valuation k (rep (y : Res k c)) * valuation k (rep ((y⁻¹ : (Res k c)ˣ) : Res k c)) := by
        rw [← map_mul]; simpa [rep] using hone.symm
    _ ≤ valuation k (rep (y : Res k c)) * 1 := by gcongr
    _ = valuation k (rep (y : Res k c)) := mul_one _

theorem rep_ne_zero {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) : rep (y : Res k c) ≠ 0 := by
  intro h
  have h1 := val_rep_unit hϖ hc y
  rw [h, map_zero] at h1
  exact zero_ne_one h1

def uRep {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) : kˣ := Units.mk0 _ (rep_ne_zero hϖ hc y)

@[simp] theorem coe_uRep {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) :
    (uRep hϖ hc y : k) = rep (y : Res k c) := rfl

theorem psi_congr {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y)
    (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1) {a b : k} (h : valuation k (a - b) ≤ 1) : ψl a = ψl b := by
  calc ψl a = ψl (b + (a - b)) := by congr 1; ring
    _ = ψl b * ψl (a - b) := hadd _ _
    _ = ψl b := by rw [hO _ h, mul_one]

theorem nu_congr {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν) {a b : kˣ}
    (hb : valuation k (b : k) = 1) (h : valuation k ((a : k) - b) ≤ valuation k (ϖ : k) ^ c) : ν a = ν b := by
  have hlt : valuation k ((a : k) - b) < valuation k (b : k) := by
    rw [hb]; exact lt_of_le_of_lt h (val_pow_lt_one hϖ hc1)
  have ha : valuation k (a : k) = 1 := by
    have e : (a : k) = ((a : k) - b) + b := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ hlt, hb]
  have hmem : a * b⁻¹ ∈ unitCong (ϖ ^ c) := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ha, hb, inv_one, mul_one]
    · have e : (a : k) * (b : k)⁻¹ - 1 = ((a : k) - b) * (b : k)⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ b.ne_zero]
      rw [Units.val_mul, Units.val_inv_eq_inv_val, e, map_mul, map_inv₀, hb, inv_one, mul_one,
        Units.val_pow_eq_pow_val, map_pow]
      exact h
  have h1 := hc _ hmem
  calc ν a = ν (a * b⁻¹ * b) := by rw [inv_mul_cancel_right]
    _ = ν (a * b⁻¹) * ν b := map_mul _ _ _
    _ = ν b := by rw [h1, one_mul]

end Generic
end PositivityTheory.ThK.GaussNe

namespace PositivityTheory.ThK.GaussNe
section Sums

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

def gS (ψl : k → ℂ) (ν : kˣ →* ℂˣ) {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (x : k) : ℂ :=
  ∑ y : (Res k c)ˣ, (((ν (uRep hϖ hc y))⁻¹ : ℂˣ) : ℂ) * ψl (x * rep (y : Res k c) / (ϖ : k) ^ c)

variable {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y) (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1)
  {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν)
include hadd hO hc

open Classical in

theorem gS_mul_unit (x : k) (hx : valuation k x ≤ 1) (u : kˣ) (hu : valuation k (u : k) = 1) :
    gS ψl ν hϖ hc1 (x * u) = ν u * gS ψl ν hϖ hc1 x := by
  classical
  have hu1 : valuation k (u : k) ≤ 1 := hu.le
  have hui : valuation k ((u⁻¹ : kˣ) : k) ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  let uO : 𝒪[k]ˣ := ⟨⟨u, hu1⟩, ⟨((u⁻¹ : kˣ) : k), hui⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  let ub : (Res k c)ˣ := Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c)).toMonoidHom uO
  have hϖ0 : valuation k (ϖ : k) ≠ 0 := (valuation k).ne_zero_iff.2 ϖ.ne_zero
  have hpos : 0 < valuation k (ϖ : k) ^ c := zero_lt_iff.2 (pow_ne_zero _ hϖ0)
  have hcong : ∀ y : (Res k c)ˣ, valuation k (rep ((y * ub : (Res k c)ˣ) : Res k c) - rep (y : Res k c) * (u : k))
      ≤ valuation k (ϖ : k) ^ c := by
    intro y
    have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) (Quotient.out ((y * ub : (Res k c)ˣ) : Res k c)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) (Quotient.out (y : Res k c) * (uO : 𝒪[k])) := by
      have h1 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c)
          (Quotient.out ((y * ub : (Res k c)ˣ) : Res k c)) = ((y * ub : (Res k c)ˣ) : Res k c) := Quotient.out_eq _
      have h2 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) (Quotient.out (y : Res k c)) =
          (y : Res k c) := Quotient.out_eq _
      rw [h1, map_mul, h2, Units.val_mul]
      rfl
    have := (mk_eq_mk_iff hϖ c _ _).1 hmk
    simpa [rep, uO] using this
  have hterm : ∀ y : (Res k c)ˣ,
      (((ν (uRep hϖ hc1 (y * ub)))⁻¹ : ℂˣ) : ℂ) * ψl (x * rep ((y * ub : (Res k c)ˣ) : Res k c) / (ϖ : k) ^ c)
        = (((ν u)⁻¹ : ℂˣ) : ℂ) * ((((ν (uRep hϖ hc1 y))⁻¹ : ℂˣ) : ℂ) *
          ψl (x * u * rep (y : Res k c) / (ϖ : k) ^ c)) := by
    intro y
    have hn : ν (uRep hϖ hc1 (y * ub)) = ν (uRep hϖ hc1 y * u) := by
      apply nu_congr hϖ hc1 hc
      · rw [Units.val_mul, map_mul, coe_uRep, val_rep_unit hϖ hc1, hu, one_mul]
      · rw [Units.val_mul, coe_uRep, coe_uRep]
        exact hcong y
    have hp : ψl (x * rep ((y * ub : (Res k c)ˣ) : Res k c) / (ϖ : k) ^ c) =
        ψl (x * u * rep (y : Res k c) / (ϖ : k) ^ c) := by
      apply psi_congr hadd hO
      have e : x * rep ((y * ub : (Res k c)ˣ) : Res k c) / (ϖ : k) ^ c - x * u * rep (y : Res k c) / (ϖ : k) ^ c
          = x * ((rep ((y * ub : (Res k c)ˣ) : Res k c) - rep (y : Res k c) * u) / (ϖ : k) ^ c) := by ring
      rw [e, map_mul, map_div₀, map_pow]
      have h2 : valuation k (rep ((y * ub : (Res k c)ˣ) : Res k c) - rep (y : Res k c) * u) /
          valuation k (ϖ : k) ^ c ≤ 1 := (div_le_one₀ hpos).2 (hcong y)
      calc _ ≤ (1 : ValueGroupWithZero k) * 1 := by gcongr
        _ = 1 := one_mul 1
    rw [hn, hp, map_mul, mul_inv, Units.val_mul]
    ring
  have hsum : gS ψl ν hϖ hc1 x = (((ν u)⁻¹ : ℂˣ) : ℂ) * gS ψl ν hϖ hc1 (x * u) := by
    simp only [gS]
    rw [← Equiv.sum_comp (Equiv.mulRight ub), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => hterm y)
  rw [hsum, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

open Classical in

theorem gS_eq_zero_of_lt (hmin : ∃ u ∈ unitCong (ϖ ^ (c - 1)), ν u ≠ 1) (x : k) (hx : valuation k x < 1) :
    gS ψl ν hϖ hc1 x = 0 := by
  classical
  obtain ⟨u0, hu0, hne⟩ := hmin
  have hu0v : valuation k (u0 : k) = 1 := hu0.1
  have hu0c : valuation k ((u0 : k) - 1) ≤ valuation k (((ϖ ^ (c - 1) : kˣ)) : k) := hu0.2
  have hϖ0 : valuation k (ϖ : k) ≠ 0 := (valuation k).ne_zero_iff.2 ϖ.ne_zero
  have hϖpos : 0 < valuation k (ϖ : k) := zero_lt_iff.2 hϖ0
  have hxle : valuation k x ≤ valuation k (ϖ : k) := by
    have hx1 : valuation k x ≤ 1 := hx.le
    let xO : 𝒪[k] := ⟨x, hx1⟩
    have hxm : xO ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨w, hw⟩ := hu.exists_right_inv
      have h1 : valuation k (x * (w : k)) = 1 := by
        have := congrArg (fun z : 𝒪[k] => valuation k (z : k)) hw
        simpa [xO] using this
      rw [map_mul] at h1
      have hw1 : valuation k (w : k) ≤ 1 := w.2
      have hlt : valuation k x * valuation k (w : k) < 1 :=
        calc valuation k x * valuation k (w : k) ≤ valuation k x * 1 := by gcongr
          _ < 1 := by rw [mul_one]; exact hx
      exact absurd h1 (ne_of_lt hlt)
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton,
      (Valuation.integer.integers (valuation k)).dvd_iff_le] at hxm
    exact hxm
  have hmul := gS_mul_unit hadd hO hϖ hc1 hc x hx.le u0 hu0v
  have hc' : (ϖ : k) ^ c = (ϖ : k) * (ϖ : k) ^ (c - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have heq : gS ψl ν hϖ hc1 (x * u0) = gS ψl ν hϖ hc1 x := by
    simp only [gS]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    congr 1
    apply psi_congr hadd hO
    have e : x * (u0 : k) * rep (y : Res k c) / (ϖ : k) ^ c - x * rep (y : Res k c) / (ϖ : k) ^ c
        = (x / (ϖ : k)) * (((u0 : k) - 1) / (ϖ : k) ^ (c - 1)) * rep (y : Res k c) := by
      rw [hc']
      have : (ϖ : k) ≠ 0 := ϖ.ne_zero
      field_simp
    rw [e, map_mul, map_mul, map_div₀, map_div₀, map_pow]
    have h1 : valuation k x / valuation k (ϖ : k) ≤ 1 := (div_le_one₀ hϖpos).2 hxle
    have h2 : valuation k ((u0 : k) - 1) / valuation k (ϖ : k) ^ (c - 1) ≤ 1 := by
      rw [div_le_one₀ (zero_lt_iff.2 (pow_ne_zero _ hϖ0))]
      simpa [Units.val_pow_eq_pow_val, map_pow] using hu0c
    have h3 := rep_le_one (y : Res k c)
    calc _ ≤ (1 : ValueGroupWithZero k) * 1 * 1 := by gcongr
      _ = 1 := by rw [one_mul, one_mul]
  have h0 : ((ν u0 : ℂ) - 1) * gS ψl ν hϖ hc1 x = 0 := by
    rw [sub_mul, ← hmul, heq, one_mul, sub_self]
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd (Units.val_eq_one.1 (sub_eq_zero.1 h)) hne
  · exact h

end Sums
end PositivityTheory.ThK.GaussNe

namespace PositivityTheory.ThK.GaussNe
section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

theorem gS_one_ne_zero {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y)
    (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1)
    (hcond : ∀ x : k, (∀ y : k, valuation k y ≤ 1 → ψl (x * y) = 1) → valuation k x ≤ 1)
    {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν)
    (hmin : ∃ u ∈ unitCong (ϖ ^ (c - 1)), ν u ≠ 1) : gS ψl ν hϖ hc1 1 ≠ 0 := by
  classical
  intro hG
  have hpos : 0 < valuation k (ϖ : k) ^ c :=
    zero_lt_iff.2 (pow_ne_zero _ ((valuation k).ne_zero_iff.2 ϖ.ne_zero))
  have hψ0 : ψl 0 = 1 := hO 0 (by simp)
  have hzero : ∀ x : k, valuation k x ≤ 1 → gS ψl ν hϖ hc1 x = 0 := by
    intro x hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact gS_eq_zero_of_lt hadd hO hϖ hc1 hc hmin x hlt
    · have hx0 : x ≠ 0 := by
        intro h
        rw [h, map_zero] at heq
        exact zero_ne_one heq
      have hm := gS_mul_unit hadd hO hϖ hc1 hc 1 (by simp) (Units.mk0 x hx0) (by simpa using heq)
      simp only [one_mul, Units.val_mk0] at hm
      rw [hm, hG, mul_zero]
  have horth : ∀ d : k, valuation k d ≤ 1 → valuation k (ϖ : k) ^ c < valuation k d →
      ∑ x : Res k c, ψl (rep x * d / (ϖ : k) ^ c) = 0 := by
    intro d hd1 hdlt
    have hz : ¬ valuation k (d / (ϖ : k) ^ c) ≤ 1 := by
      rw [map_div₀, map_pow, not_le, lt_div_iff₀ hpos, one_mul]
      exact hdlt
    obtain ⟨t, ht1, htne⟩ : ∃ t : k, valuation k t ≤ 1 ∧ ψl (d / (ϖ : k) ^ c * t) ≠ 1 := by
      by_contra hno
      push Not at hno
      exact hz (hcond _ hno)
    let tb : Res k c := Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) (⟨t, ht1⟩ : 𝒪[k])
    have hshift : ∀ x : Res k c, ψl (rep (x + tb) * d / (ϖ : k) ^ c) =
        ψl (rep x * d / (ϖ : k) ^ c) * ψl (d / (ϖ : k) ^ c * t) := by
      intro x
      have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) (Quotient.out (x + tb)) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) (Quotient.out x + (⟨t, ht1⟩ : 𝒪[k])) := by
        rw [map_add]
        rw [show Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) (Quotient.out (x + tb)) = x + tb from
            Quotient.out_eq _,
          show Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) (Quotient.out x) = x from Quotient.out_eq _]
      have hv := (mk_eq_mk_iff hϖ c _ _).1 hmk
      rw [← hadd]
      apply psi_congr hadd hO
      have e : rep (x + tb) * d / (ϖ : k) ^ c - (rep x * d / (ϖ : k) ^ c + d / (ϖ : k) ^ c * t)
          = ((((Quotient.out (x + tb) : 𝒪[k]) : k) - (((Quotient.out x + (⟨t, ht1⟩ : 𝒪[k])) : 𝒪[k]) : k)) /
            (ϖ : k) ^ c) * d := by
        simp only [rep]
        push_cast
        ring
      rw [e, map_mul, map_div₀, map_pow]
      have h2 : valuation k ((((Quotient.out (x + tb) : 𝒪[k]) : k) -
          (((Quotient.out x + (⟨t, ht1⟩ : 𝒪[k])) : 𝒪[k]) : k))) / valuation k (ϖ : k) ^ c ≤ 1 :=
        (div_le_one₀ hpos).2 hv
      calc _ ≤ (1 : ValueGroupWithZero k) * 1 := by gcongr
        _ = 1 := one_mul 1
    have hsum : ∑ x : Res k c, ψl (rep x * d / (ϖ : k) ^ c) =
        (∑ x : Res k c, ψl (rep x * d / (ϖ : k) ^ c)) * ψl (d / (ϖ : k) ^ c * t) := by
      rw [Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight tb)]
      exact Finset.sum_congr rfl (fun x _ => hshift x)
    have h0 : (∑ x : Res k c, ψl (rep x * d / (ϖ : k) ^ c)) * (ψl (d / (ϖ : k) ^ c * t) - 1) = 0 := by
      rw [mul_sub, mul_one, ← hsum, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) htne
  have key : ∑ x : Res k c, gS ψl ν hϖ hc1 (rep x) *
      ψl (-(rep x * rep ((1 : (Res k c)ˣ) : Res k c)) / (ϖ : k) ^ c) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [hzero _ (rep_le_one x), zero_mul]
  simp only [gS, Finset.sum_mul] at key
  rw [Finset.sum_comm] at key
  have inner : ∀ y : (Res k c)ˣ, ∑ x : Res k c, (((ν (uRep hϖ hc1 y))⁻¹ : ℂˣ) : ℂ) *
      ψl (rep x * rep (y : Res k c) / (ϖ : k) ^ c) *
      ψl (-(rep x * rep ((1 : (Res k c)ˣ) : Res k c)) / (ϖ : k) ^ c)
      = (((ν (uRep hϖ hc1 y))⁻¹ : ℂˣ) : ℂ) *
        ∑ x : Res k c, ψl (rep x * (rep (y : Res k c) - rep ((1 : (Res k c)ˣ) : Res k c)) / (ϖ : k) ^ c) := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [mul_assoc, ← hadd]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun y _ => inner y)] at key
  rw [Finset.sum_eq_single (1 : (Res k c)ˣ)] at key
  · simp only [sub_self, mul_zero, zero_div, hψ0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at key
    rcases mul_eq_zero.1 key with h | h
    · exact Units.ne_zero _ h
    · exact (Nat.cast_ne_zero.2 Fintype.card_ne_zero) h
  · intro y _ hy
    have hd1 : valuation k (rep (y : Res k c) - rep ((1 : (Res k c)ˣ) : Res k c)) ≤ 1 :=
      le_trans ((valuation k).map_sub _ _) (max_le (rep_le_one _) (rep_le_one _))
    have hdlt : valuation k (ϖ : k) ^ c <
        valuation k (rep (y : Res k c) - rep ((1 : (Res k c)ˣ) : Res k c)) := by
      by_contra hle
      push Not at hle
      apply hy
      apply Units.ext
      have hm := (mk_eq_mk_iff hϖ c (Quotient.out (y : Res k c))
        (Quotient.out ((1 : (Res k c)ˣ) : Res k c))).2 hle
      rwa [show Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) (Quotient.out (y : Res k c)) =
          (y : Res k c) from Quotient.out_eq _,
        show Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c)
          (Quotient.out ((1 : (Res k c)ˣ) : Res k c)) = ((1 : (Res k c)ˣ) : Res k c) from Quotient.out_eq _] at hm
    rw [horth _ hd1 hdlt, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_condLE {ϖ : kˣ} (hϖ : IsUnif ϖ) (ν : kˣ →* ℂˣ) (hν : Continuous fun x : kˣ => (ν x : ℂ)) :
    ∃ e, CondLE ϖ e ν := by
  have hϖ1 : valuation k (ϖ : k) < 1 := by
    have := val_pow_lt_one hϖ (c := 1) le_rfl
    simpa using this
  have hS : {x : kˣ | ‖(ν x : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : kˣ) := by
    filter_upwards [hν.continuousAt (x := 1) (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))]
      with x hx
    simpa [dist_eq_norm] using hx
  have hemb : Topology.IsEmbedding (Units.val : kˣ → k) := Units.isEmbedding_val₀
  rw [hemb.toIsInducing.nhds_eq_comap, Filter.mem_comap] at hS
  obtain ⟨T, hT, hTS⟩ := hS
  obtain ⟨γ, -, hγ⟩ := (IsValuativeTopology.hasBasis_nhds ((1 : kˣ) : k)).mem_iff.1 hT
  obtain ⟨e, he⟩ := exists_pow_lt₀ hϖ1 γ
  have hU : ∀ y ∈ unitCong (ϖ ^ e), ‖(ν y : ℂ) - 1‖ < 1 / 2 := by
    intro y hy
    apply hTS
    show (y : k) ∈ T
    apply hγ
    show valuation k ((y : k) - 1) < γ
    calc valuation k ((y : k) - 1) ≤ valuation k (((ϖ ^ e : kˣ)) : k) := hy.2
      _ = valuation k (ϖ : k) ^ e := by rw [Units.val_pow_eq_pow_val, map_pow]
      _ < γ := he
  refine ⟨e, fun x hx => ?_⟩
  have hpow : ∀ n : ℕ, ‖((ν x : ℂ)) ^ n - 1‖ < 1 / 2 := by
    intro n
    have := hU (x ^ n) (Subgroup.pow_mem _ hx n)
    simpa [map_pow, Units.val_pow_eq_pow_val] using this
  by_contra hne
  have hne' : (ν x : ℂ) ≠ 1 := fun h => hne (Units.ext h)
  set z := (ν x : ℂ) with hz
  have hd : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne')
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have hre : ∀ n : ℕ, 1 / 2 < (z ^ n).re := by
    intro n
    have h1 := hpow n
    have h2 : |(z ^ n - 1).re| ≤ ‖z ^ n - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h2
    linarith [(abs_lt.1 (lt_of_le_of_lt h2 h1)).1]
  have hNpos : 0 < N := by
    have h0 : (0 : ℝ) < 1 / ‖z - 1‖ := by positivity
    exact_mod_cast lt_trans h0 hN
  have hlow : (N : ℝ) / 2 < ‖∑ n ∈ Finset.range N, z ^ n‖ := by
    have h1 : (N : ℝ) / 2 = ∑ n ∈ Finset.range N, (1 / 2 : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    have h2 : ∑ n ∈ Finset.range N, (1 / 2 : ℝ) < ∑ n ∈ Finset.range N, (z ^ n).re :=
      Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 hNpos.ne') (fun n _ => hre n)
    rw [h1]
    calc _ < ∑ n ∈ Finset.range N, (z ^ n).re := h2
      _ = (∑ n ∈ Finset.range N, z ^ n).re := (Complex.re_sum _ _).symm
      _ ≤ ‖∑ n ∈ Finset.range N, z ^ n‖ := Complex.re_le_norm _
  have hgeom : (∑ n ∈ Finset.range N, z ^ n) * (z - 1) = z ^ N - 1 := geom_sum_mul z N
  have hup : ‖∑ n ∈ Finset.range N, z ^ n‖ * ‖z - 1‖ < 1 / 2 := by
    rw [← norm_mul, hgeom]
    exact hpow N
  have hlt : (N : ℝ) / 2 * ‖z - 1‖ < 1 / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hlow.le hd.le) hup
  have hN' : 1 < (N : ℝ) * ‖z - 1‖ := by
    rw [div_lt_iff₀ hd] at hN
    linarith
  linarith

end Main
end PositivityTheory.ThK.GaussNe

namespace PositivityTheory.ThK.GaussNe
section Place

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locFieldPl {F : Type} [Field F] [NumberField F] (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

theorem val_le_one_iff {F : Type} [Field F] [NumberField F] (v : Pl F) (x : Fv F v) :
    valuation (Fv F v) x ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← map_one (valuation (Fv F v)),
    ← Valuation.Compatible.vle_iff_le]
  show Valued.v x ≤ Valued.v (1 : Fv F v) ↔ _
  rw [map_one]

theorem gauss_ne_zero : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (ν : (Fv F v)ˣ →* ℂˣ), PsiUnr ψ v → Continuous (fun x : (Fv F v)ˣ => (ν x : ℂ)) →
    (∃ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F ∧
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F ∧ ν x ≠ 1) → gauss ψ ν ≠ 0 := by
  intro F _ _ ψ v ν hψ hν hx
  classical
  have hϖ : IsUnif (unifAt v) := by
    show IsUnif (Exists.choose _)
    exact Exists.choose_spec _
  have hne : {c | CondLE (unifAt v) c ν}.Nonempty := exists_condLE hϖ ν hν
  have hc : CondLE (unifAt v) (condExp ν) ν := Nat.sInf_mem hne
  obtain ⟨x0, hx0a, hx0b, hx0ν⟩ := hx
  have hc1 : 1 ≤ condExp ν := by
    by_contra h0
    have hc0 : condExp ν = 0 := by omega
    apply hx0ν
    apply hc
    rw [hc0, pow_zero]
    have ha := (val_le_one_iff v _).2 hx0a
    have hb := (val_le_one_iff v _).2 hx0b
    have hv1 : valuation (Fv F v) (x0 : Fv F v) = 1 := by
      refine le_antisymm ha ?_
      have hm : valuation (Fv F v) (x0 : Fv F v) * valuation (Fv F v) ((x0⁻¹ : (Fv F v)ˣ) : Fv F v) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      calc (1 : ValueGroupWithZero (Fv F v)) = _ := hm.symm
        _ ≤ valuation (Fv F v) (x0 : Fv F v) * 1 := by gcongr
        _ = _ := mul_one _
    refine ⟨hv1, ?_⟩
    rw [Units.val_one, map_one]
    exact le_trans ((valuation (Fv F v)).map_sub _ _) (max_le ha (le_of_eq (map_one _)))
  have hmin : ∃ u ∈ unitCong (unifAt v ^ (condExp ν - 1)), ν u ≠ 1 := by
    have hnot : condExp ν - 1 ∉ {c | CondLE (unifAt v) c ν} := by
      have hlt : condExp ν - 1 < condExp ν := by omega
      first
        | exact Nat.not_mem_of_lt_sInf hlt
        | exact Nat.notMem_of_lt_sInf hlt
    by_contra hall
    push Not at hall
    exact hnot (fun u hu => hall u hu)
  have hadd : ∀ a b : Fv F v, psiLoc ψ v (a + b) = psiLoc ψ v a * psiLoc ψ v b := by
    intro a b
    have harg : (LinearMap.inr F (Ainf F) (Af F)) ((singleFin v) (a + b)) =
        (LinearMap.inr F (Ainf F) (Af F)) ((singleFin v) a) + (LinearMap.inr F (Ainf F) (Af F)) ((singleFin v) b) := by
      rw [map_add, map_add]
    exact (congrArg ψ harg).trans (ψ.map_add_eq_mul _ _)
  have hO : ∀ a : Fv F v, valuation (Fv F v) a ≤ 1 → psiLoc ψ v a = 1 := by
    intro a ha
    have h := (hψ a).2 ((val_le_one_iff v a).1 ha) 1 (v.adicCompletionIntegers F).one_mem
    simpa using h
  have hcond : ∀ a : Fv F v, (∀ y : Fv F v, valuation (Fv F v) y ≤ 1 → psiLoc ψ v (a * y) = 1) →
      valuation (Fv F v) a ≤ 1 := by
    intro a h
    rw [val_le_one_iff]
    exact (hψ a).1 (fun y hy => h y ((val_le_one_iff v y).2 hy))
  have hg := gS_one_ne_zero hadd hO hcond hϖ hc1 hc hmin
  have heq : gauss ψ ν = gS (psiLoc ψ v) ν hϖ hc1 1 := by
    delta GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.gauss gS
    refine Finset.sum_congr ?_ (fun y _ => ?_)
    · first
        | rfl
        | congr 1
        | exact Subsingleton.elim _ _
    · split_ifs with h
      · exact absurd h (rep_ne_zero hϖ hc1 y)
      · rw [one_mul]
        rfl
  rw [heq]
  exact hg

end Place
end PositivityTheory.ThK.GaussNe
