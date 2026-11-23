import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitQuotientPrimePowEqExponent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.CharValueLength

variable {l : ℕ} [Fact l.Prime] in
private theorem isUnit_of_toZMod_ne_zero' {x : ℤ_[l]} (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hx

variable {l : ℕ} [Fact l.Prime] in
private theorem principalUnit_pow_prime_eq_one_add_pow_succ {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r)
    (h2 : l = 2 → 2 ≤ r) (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ l = 1 + (l : ℤ_[l]) ^ (r + 1) * w' := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨n, hn⟩ : ∃ n, l = n + 2 := ⟨l - 2, by omega⟩
  set x := (l : ℤ_[l]) ^ r * w with hx
  have hexp : u ^ l = (∑ j ∈ Finset.range (n + 1),
      x ^ (j + 1 + 1) * ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l])) + x * l + 1 := by
    rw [hu, add_comm, add_pow, show l + 1 = n + 1 + 1 + 1 by omega, Finset.sum_range_succ',
      Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, pow_one, Nat.choose_zero_right, Nat.choose_one_right,
      Nat.cast_one, zero_add]
  have hdvd : (l : ℤ_[l]) ^ (r + 2) ∣ ∑ j ∈ Finset.range (n + 1),
      x ^ (j + 1 + 1) * ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l]) := by
    refine Finset.dvd_sum fun j hj => ?_
    have hj' : j + 2 ≤ l := by rw [Finset.mem_range] at hj; omega
    have hxp : x ^ (j + 1 + 1) = (l : ℤ_[l]) ^ (r * (j + 1 + 1)) * w ^ (j + 1 + 1) := by
      rw [hx, mul_pow, ← pow_mul]
    rcases Nat.lt_or_ge (j + 2) l with hlt | hge
    · have hc : (l : ℤ_[l]) ∣ ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l]) :=
        Nat.cast_dvd_cast ((Fact.out : l.Prime).dvd_choose_self (by omega) (by omega))
      have h1 : (l : ℤ_[l]) ^ (r + 2) ∣ (l : ℤ_[l]) ^ (r * (j + 1 + 1)) * l := by
        rw [← pow_succ]; exact pow_dvd_pow _ (by nlinarith)
      exact h1.trans (mul_dvd_mul (Dvd.intro _ hxp.symm) hc)
    · have hle : r + 2 ≤ r * (j + 1 + 1) := by
        rcases Nat.lt_or_ge l 3 with h | h
        · have := h2 (by omega); nlinarith
        · nlinarith
      exact ((pow_dvd_pow _ hle).trans (Dvd.intro _ hxp.symm)).mul_right _
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨w + l * c, isUnit_of_toZMod_ne_zero' ?_, ?_⟩
  · simpa [ZMod.natCast_self] using (hw.map PadicInt.toZMod).ne_zero
  · rw [hexp, hc, hx]; ring

variable {l : ℕ} [Fact l.Prime] in
private theorem toZMod_principalUnit_eq_one {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r)
    (hu : u = 1 + (l : ℤ_[l]) ^ r * w) : PadicInt.toZMod u = 1 := by
  rw [hu]
  simp [ZMod.natCast_self, zero_pow (Nat.one_le_iff_ne_zero.1 hr)]

variable {l : ℕ} [Fact l.Prime] in
private theorem principalUnit_pow_of_not_dvd {u w : ℤ_[l]} {r m : ℕ} (hr : 1 ≤ r)
    (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) (hm : ¬ l ∣ m) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ m = 1 + (l : ℤ_[l]) ^ r * w' := by
  refine ⟨w * ∑ i ∈ Finset.range m, u ^ i, hw.mul (isUnit_of_toZMod_ne_zero' ?_), ?_⟩
  · rw [map_sum]
    simp only [map_pow, toZMod_principalUnit_eq_one hr hu, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    exact fun h => hm ((ZMod.natCast_eq_zero_iff m l).1 h)
  · have hg := geom_sum_mul u m
    have hu1 : u - 1 = (l : ℤ_[l]) ^ r * w := by rw [hu]; ring
    rw [hu1] at hg
    linear_combination -hg

variable {l : ℕ} [Fact l.Prime] in
private theorem principalUnit_pow_eq_one_add_pow_add_padicValNat {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r) (h2 : l = 2 → 2 ≤ r)
    (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) {k : ℕ} (hk : k ≠ 0) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ k = 1 + (l : ℤ_[l]) ^ (r + padicValNat l k) * w' := by
  have hpow : ∀ a : ℕ, ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ (l ^ a) = 1 + (l : ℤ_[l]) ^ (r + a) * w' := by
    intro a
    induction a with
    | zero => exact ⟨w, hw, by simpa using hu⟩
    | succ a ih =>
      obtain ⟨w', hw', h'⟩ := ih
      obtain ⟨w'', hw'', h''⟩ :=
        principalUnit_pow_prime_eq_one_add_pow_succ (by omega) (fun h => by have := h2 h; omega) hw' h'
      exact ⟨w'', hw'', by rw [pow_succ, pow_mul, h'', ← add_assoc]⟩
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk l (Fact.out : l.Prime).one_lt.ne'
  obtain ⟨w', hw', h'⟩ := hpow a
  obtain ⟨w'', hw'', h''⟩ := principalUnit_pow_of_not_dvd (by omega) hw' h' hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero l)
  refine ⟨w'', hw'', ?_⟩
  rw [padicValNat.mul (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero, pow_mul, h'']

private theorem length_quotient_span_unit_mul_pow_eq {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) (w : Oˣ) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {(w : O) * ϖ ^ n}) = n := by
  rw [Ideal.span_singleton_mul_left_unit w.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O n

theorem _root_.GlobalTheory.CharValueLength.injOn_and_lenUnit : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [CharZero O] (s t : ℕ) (u v : ℤ_[l]ˣ) (χ : ℕ → Oˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s * (v : ℤ_[l]) → (∀ c : ℕ, 1 ≤ c → c ≤ t → χ c = χ 1 * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (-((c : ℤ) - 1))) → Set.InjOn (fun c => (χ c : O)) (Finset.Icc 1 t : Set ℕ) ∧ _root_.Formalism.BasicNotions.lenUnit (O := O) l (O ⧸ Ideal.span {∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - (χ c : O))}) = ∑ k ∈ Finset.Ioo 0 t, ((s : ℚ) + padicValNat l k) := by
  intro l _ O _ _ _ _ _ _ s t u v χ hs hs2 huv hχ
  have hl0 : (l : O) ≠ 0 := _root_.GlobalTheory.LenUnitPow.natCast_ne_zero l
  have hD : ∀ k : ℕ, k ≠ 0 → ∃ ε : Oˣ,
      algebraMap ℤ_[l] O u ^ k - 1 = ε * (l : O) ^ (s + padicValNat l k) := by
    intro k hk
    obtain ⟨w', hw', h'⟩ := principalUnit_pow_eq_one_add_pow_add_padicValNat hs hs2 v.isUnit huv hk
    refine ⟨(hw'.map (algebraMap ℤ_[l] O)).unit, ?_⟩
    rw [IsUnit.unit_spec, ← map_pow, h', map_add, map_one, map_mul, map_pow, map_natCast]
    ring
  have hrel : ∀ c, 1 ≤ c → c ≤ t → (χ c : O) * algebraMap ℤ_[l] O u ^ (c - 1) = χ 1 := by
    intro c h1 h2
    have h : χ c * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (c - 1) = χ 1 := by
      rw [hχ c h1 h2, mul_assoc, ← zpow_natCast, ← zpow_add, Nat.cast_sub h1, Nat.cast_one,
        neg_add_cancel, zpow_zero, mul_one]
    have h' := congrArg (fun z : Oˣ => (z : O)) h
    simpa using h'
  have hφu : IsUnit (algebraMap ℤ_[l] O u) := u.isUnit.map _
  constructor
  · intro c hc c' hc' heq
    simp only [Finset.coe_Icc, Set.mem_Icc] at hc hc'
    simp only at heq
    have key : ∀ a b : ℕ, 1 ≤ a ∧ a ≤ t → 1 ≤ b ∧ b ≤ t → (χ a : O) = χ b → a ≤ b → a = b := by
      intro c c' hc hc' heq hle
      by_contra hne
      obtain ⟨ε, hε⟩ := hD (c' - c) (by omega)
      have e1 := hrel c hc.1 hc.2
      have e2 := hrel c' hc'.1 hc'.2
      rw [← heq, show c' - 1 = (c - 1) + (c' - c) by omega, pow_add] at e2
      have h0 : (χ c : O) * algebraMap ℤ_[l] O u ^ (c - 1) *
          (algebraMap ℤ_[l] O u ^ (c' - c) - 1) = 0 := by
        linear_combination e2 - e1
      rcases mul_eq_zero.1 h0 with h | h
      · exact ((χ c).isUnit.mul (hφu.pow _)).ne_zero h
      · rw [hε] at h
        exact mul_ne_zero ε.ne_zero (pow_ne_zero _ hl0) h
    rcases le_total c c' with hle | hle
    · exact key c c' hc hc' heq hle
    · exact (key c' c hc' hc heq.symm hle).symm
  · have hterm : ∀ c ∈ Finset.Ioc 1 t, ∃ ε : Oˣ,
        (χ 1 : O) - χ c = ε * (l : O) ^ (s + padicValNat l (c - 1)) := by
      intro c hc
      rw [Finset.mem_Ioc] at hc
      obtain ⟨ε, hε⟩ := hD (c - 1) (by omega)
      refine ⟨χ c * ε, ?_⟩
      rw [← hrel c (by omega) hc.2, Units.val_mul, mul_assoc, ← hε]
      ring
    choose! ε hε using hterm
    have hprod : ∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - χ c) =
        ((∏ c ∈ Finset.Ioc 1 t, ε c : Oˣ) : O) *
          (l : O) ^ (∑ c ∈ Finset.Ioc 1 t, (s + padicValNat l (c - 1))) := by
      rw [Finset.prod_congr rfl hε, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        Units.coe_prod]
    have hsum : ∑ c ∈ Finset.Ioc 1 t, (s + padicValNat l (c - 1)) =
        ∑ k ∈ Finset.Ioo 0 t, (s + padicValNat l k) := by
      refine Finset.sum_nbij' (fun c => c - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_ <;> intro a ha <;>
        simp only [Finset.mem_Ioc, Finset.mem_Ioo] at ha ⊢ <;> omega
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨e, η, hη⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    have he : e ≠ 0 := by
      rintro rfl
      exact _root_.GlobalTheory.LenUnitPow.natCast_not_isUnit l (O := O)
        (by rw [hη, pow_zero, mul_one]; exact η.isUnit)
    unfold _root_.Formalism.BasicNotions.lenUnit
    rw [hprod, hsum, hη, mul_pow, ← pow_mul, ← mul_assoc, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, length_quotient_span_unit_mul_pow_eq hϖ, length_quotient_span_unit_mul_pow_eq hϖ,
      ENat.toNat_natCast, ENat.toNat_natCast, Nat.cast_mul,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 he)]
    push_cast
    rfl

end GlobalTheory.CharValueLength
