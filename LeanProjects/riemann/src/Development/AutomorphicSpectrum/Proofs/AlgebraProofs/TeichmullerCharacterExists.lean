import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.RbFund

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem fund_ex_relay : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∃ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) := by
  intro p hpF C _ _ _ v R _ _ hR hp F _ _ _ _ f hq
  classical
  have hpp : p.Prime := hpF.out
  have hf : f ≠ 0 := by
    rintro rfl
    have h1 : 1 < Fintype.card F := by
      first
        | exact Fintype.one_lt_card
        | exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hq, pow_zero] at h1
    exact lt_irrefl _ h1
  have hqpos : 0 < p ^ f := Nat.pos_of_ne_zero (pow_ne_zero _ hpp.ne_zero)
  obtain ⟨n, hqn⟩ : ∃ n, p ^ f = n + 1 := ⟨p ^ f - 1, by omega⟩
  have hn : 0 < n := by
    have h2 : p ≤ p ^ f := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hpp.pos (Nat.one_le_iff_ne_zero.mpr hf)
    have := hpp.two_le
    omega

  have L1 : ∀ x : R, v (algebraMap R C x) = 1 → IsUnit x := by
    intro x hx
    apply hR.isUnit_of_one _ hx
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, map_zero] at hx
    exact zero_ne_one hx
  have hpnu : ¬ IsUnit (p : R) := by
    intro hu
    have h1 := hR.one_of_isUnit hu
    rw [map_natCast] at h1
    rw [h1] at hp
    exact lt_irrefl _ hp
  obtain ⟨M, hM, hpM⟩ := Ideal.exists_le_maximal (Ideal.span {(p : R)}) (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hpnu)
  have hpM' : (p : R) ∈ M := hpM (Ideal.mem_span_singleton.mpr (dvd_refl _))
  have L2 : ∀ m ∈ M, v (algebraMap R C m) < 1 := by
    intro m hm
    refine lt_of_le_of_ne (hR.map_le_one m) ?_
    intro h1
    apply hM.ne_top
    rw [Ideal.eq_top_iff_one]
    obtain ⟨w, hw⟩ := (L1 m h1).exists_left_inv
    rw [← hw]
    exact M.mul_mem_left w hm
  have LU : ∀ x : R, x ∉ M → IsUnit x := by
    intro x hx
    obtain ⟨y, i, hi, hyi⟩ := hM.exists_inv hx
    have h1 : y * x = 1 - i := by rw [← hyi]; ring
    have h2 : v (algebraMap R C (y * x)) = 1 := by
      rw [h1, map_sub, map_one]
      exact v.map_one_sub_of_lt (L2 i hi)
    exact isUnit_of_mul_isUnit_right (L1 _ h2)

  let _instK : Field (R ⧸ M) := Ideal.Quotient.field M
  have hmk0 : ∀ x : R, Ideal.Quotient.mk M x = 0 ↔ x ∈ M := by
    intro x
    rw [← map_zero (Ideal.Quotient.mk M), Ideal.Quotient.eq, sub_zero]
  have hk : CharP (R ⧸ M) p := by
    rw [CharP.charP_iff_prime_eq_zero hpp, ← map_natCast (Ideal.Quotient.mk M) p]
    exact (hmk0 _).mpr hpM'

  have H : ∀ s t : R, t ^ (p ^ f) = t → s - t ∈ M →
      ∃ u : R, IsUnit u ∧ s ^ (p ^ f) - s = (s - t) * u := by
    intro s t ht hst
    set G := ∑ i ∈ Finset.range (p ^ f), s ^ i * t ^ (p ^ f - 1 - i) with hG
    refine ⟨G - 1, ?_, ?_⟩
    · apply LU
      intro hG1
      have hGM : G ∈ M := by
        rw [← hmk0]
        have hst' : Ideal.Quotient.mk M s = Ideal.Quotient.mk M t := Ideal.Quotient.eq.mpr hst
        rw [hG, map_sum]
        simp only [map_mul, map_pow, hst']
        have hsum : ∑ i ∈ Finset.range (p ^ f), Ideal.Quotient.mk M t ^ i * Ideal.Quotient.mk M t ^ (p ^ f - 1 - i)
            = ∑ i ∈ Finset.range (p ^ f), Ideal.Quotient.mk M t ^ (p ^ f - 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← pow_add]
          congr 1
          have := Finset.mem_range.mp hi
          omega
        have hc : ((p ^ f : ℕ) : R ⧸ M) = 0 := by
          rw [Nat.cast_pow, CharP.cast_eq_zero (R ⧸ M) p, zero_pow hf]
        rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc, zero_mul]
      have h1M : (1 : R) ∈ M := by
        have := M.sub_mem hGM hG1
        rwa [sub_sub_cancel] at this
      apply hM.ne_top
      rw [Ideal.eq_top_iff_one]
      exact h1M
    · have hgs := geom_sum₂_mul s t (p ^ f)
      rw [← hG] at hgs
      rw [mul_sub, mul_one, mul_comm (s - t) G, hgs, ht]
      ring
  have Uq : ∀ t1 t2 : R, t1 ^ (p ^ f) = t1 → t2 ^ (p ^ f) = t2 →
      Ideal.Quotient.mk M t1 = Ideal.Quotient.mk M t2 → t1 = t2 := by
    intro t1 t2 h1 h2 h12
    obtain ⟨u, hu, hsu⟩ := H t1 t2 h2 (Ideal.Quotient.eq.mp h12)
    rw [h1, sub_self] at hsu
    have h3 : (t1 - t2) * u = 0 := hsu.symm
    exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp h3)

  have : NeZero ((n : ℕ) : C) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n C) (by
    first
      | exact (Polynomial.degree_cyclotomic_pos n C hn).ne'
      | (rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hn).ne'))
  have hζp : IsPrimitiveRoot ζ n := (Polynomial.isRoot_cyclotomic_iff).mp hζ
  have hζ1 : v ζ ≤ 1 := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 := one_lt_pow₀ hlt hn.ne'
    rw [← v.map_pow, hζp.pow_eq_one, v.map_one] at h1
    exact lt_irrefl _ h1
  obtain ⟨z, hz⟩ := hR.exists_of_le_one hζ1
  have hzn : z ^ n = 1 := hR.hom_inj (by rw [map_pow, hz, hζp.pow_eq_one, map_one])
  have hTz : ∀ i : ℕ, (z ^ i) ^ (p ^ f) = z ^ i := by
    intro i
    rw [hqn, pow_succ, ← pow_mul, mul_comm i n, pow_mul, hzn, one_pow, one_mul]
  have hrr : IsPrimitiveRoot (Ideal.Quotient.mk M z) n := by
    refine IsPrimitiveRoot.mk_of_lt _ hn ?_ ?_
    · rw [← map_pow, hzn, map_one]
    · intro l hl0 hln hl1
      have h1 : z ^ l = z ^ 0 := by
        apply Uq _ _ (hTz l) (hTz 0)
        rw [map_pow, hl1, pow_zero, map_one]
      have h2 : ζ ^ l = ζ ^ 0 := by
        have h3 := congrArg (algebraMap R C) h1
        rwa [map_pow, map_pow, hz] at h3
      have := hζp.pow_inj hln hn h2
      omega
  have hrn : Ideal.Quotient.mk M z ^ n = 1 := hrr.pow_eq_one
  have hrr0 : Ideal.Quotient.mk M z ≠ 0 := by
    intro h0
    have h1 := hrn
    rw [h0, zero_pow hn.ne'] at h1
    exact zero_ne_one h1

  let S : Subfield (R ⧸ M) :=
    { carrier := {x | x ^ (p ^ f) = x}
      mul_mem' := by
        intro a b ha hb
        have ha' : a ^ (p ^ f) = a := ha
        have hb' : b ^ (p ^ f) = b := hb
        show (a * b) ^ (p ^ f) = a * b
        rw [mul_pow, ha', hb']
      one_mem' := by
        show (1 : R ⧸ M) ^ (p ^ f) = 1
        exact one_pow _
      add_mem' := by
        intro a b ha hb
        have ha' : a ^ (p ^ f) = a := ha
        have hb' : b ^ (p ^ f) = b := hb
        show (a + b) ^ (p ^ f) = a + b
        rw [add_pow_char_pow, ha', hb']
      zero_mem' := by
        show (0 : R ⧸ M) ^ (p ^ f) = 0
        exact zero_pow (pow_ne_zero _ hpp.ne_zero)
      neg_mem' := by
        intro a ha
        have ha' : a ^ (p ^ f) = a := ha
        show (-a) ^ (p ^ f) = -a
        rw [neg_eq_zero_sub, sub_pow_char_pow, ha', zero_pow (pow_ne_zero _ hpp.ne_zero)]
      inv_mem' := by
        intro a ha
        have ha' : a ^ (p ^ f) = a := ha
        show a⁻¹ ^ (p ^ f) = a⁻¹
        rw [inv_pow, ha'] }
  let φ : Option (Fin n) → R ⧸ M := fun o => Option.elim o 0 (fun i => Ideal.Quotient.mk M z ^ (i : ℕ))
  have hφ : Function.Injective φ := by
    intro o1 o2 h
    cases o1 with
    | none =>
      cases o2 with
      | none => rfl
      | some j =>
        exact absurd (show Ideal.Quotient.mk M z ^ (j : ℕ) = 0 from h.symm) (pow_ne_zero _ hrr0)
    | some i =>
      cases o2 with
      | none =>
        exact absurd (show Ideal.Quotient.mk M z ^ (i : ℕ) = 0 from h) (pow_ne_zero _ hrr0)
      | some j =>
        have hij := hrr.pow_inj i.2 j.2
          (show Ideal.Quotient.mk M z ^ (i : ℕ) = Ideal.Quotient.mk M z ^ (j : ℕ) from h)
        exact congrArg some (Fin.ext hij)
  have hdom : IsDomain (R ⧸ M) := Ideal.Quotient.isDomain M
  have hnz : NeZero n := ⟨hn.ne'⟩
  have hrange : Set.range φ = (S : Set (R ⧸ M)) := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none =>
        show (0 : R ⧸ M) ^ (p ^ f) = 0
        exact zero_pow (pow_ne_zero _ hpp.ne_zero)
      | some i =>
        show (Ideal.Quotient.mk M z ^ (i : ℕ)) ^ (p ^ f) = Ideal.Quotient.mk M z ^ (i : ℕ)
        rw [hqn, pow_succ, ← pow_mul, mul_comm (i : ℕ) n, pow_mul, hrn, one_pow, one_mul]
    · intro hx
      have hx' : x ^ (p ^ f) = x := hx
      by_cases h0 : x = 0
      · exact ⟨none, h0.symm⟩
      · have hxn : x ^ n = 1 := by
          rw [hqn, pow_succ] at hx'
          exact mul_right_cancel₀ h0 (hx'.trans (one_mul x).symm)
        obtain ⟨i, hi, hix⟩ := hrr.eq_pow_of_pow_eq_one hxn
        exact ⟨some ⟨i, hi⟩, hix⟩
  let E : Option (Fin n) ≃ S := (Equiv.ofInjective φ hφ).trans (Equiv.setCongr hrange)
  let _instS : Fintype S := Fintype.ofEquiv _ E
  have hcardS : Fintype.card S = Fintype.card F := by
    rw [← Fintype.card_congr E, Fintype.card_option, Fintype.card_fin, hq, hqn]
  let e : F ≃+* S := FiniteField.ringEquivOfCardEq hcardS.symm

  have hlift : ∀ x : S, ∃ t : R, t ^ (p ^ f) = t ∧ Ideal.Quotient.mk M t = (x : R ⧸ M) := by
    intro x
    obtain ⟨o, ho⟩ : (x : R ⧸ M) ∈ Set.range φ := by rw [hrange]; exact x.2
    cases o with
    | none => exact ⟨0, zero_pow (pow_ne_zero _ hpp.ne_zero), by rw [map_zero]; exact ho⟩
    | some i => exact ⟨z ^ (i : ℕ), hTz i, by rw [map_pow]; exact ho⟩
  let σf : F → R := fun a => Classical.choose (hlift (e a))
  have hs1 : ∀ a, (σf a) ^ (p ^ f) = σf a := fun a => (Classical.choose_spec (hlift (e a))).1
  have hs2 : ∀ a, Ideal.Quotient.mk M (σf a) = ((e a : S) : R ⧸ M) :=
    fun a => (Classical.choose_spec (hlift (e a))).2
  have hone : σf 1 = 1 := by
    refine Uq _ _ (hs1 1) (one_pow _) ?_
    simp only [hs2, map_one, Subfield.coe_one]
  have hzero : σf 0 = 0 := by
    refine Uq _ _ (hs1 0) (zero_pow (pow_ne_zero _ hpp.ne_zero)) ?_
    simp only [hs2, map_zero, Subfield.coe_zero]
  have hmul : ∀ a b, σf (a * b) = σf a * σf b := by
    intro a b
    refine Uq _ _ (hs1 _) ?_ ?_
    · rw [mul_pow, hs1, hs1]
    · simp only [hs2, map_mul, Subfield.coe_mul]
  let σ : MulChar F R :=
    { toFun := σf
      map_one' := hone
      map_mul' := hmul
      map_nonunit' := by
        intro a ha
        have ha0 : a = 0 := by
          by_contra h
          exact ha (isUnit_iff_ne_zero.mpr h)
        subst ha0
        exact hzero }
  refine ⟨σ, fun a b => ?_⟩
  show σf (a + b) - σf a - σf b ∈ Ideal.span {(p : R)}
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hpp (σf a) (σf b) f
  have hst : σf a + σf b - σf (a + b) ∈ M := by
    rw [← Ideal.Quotient.eq]
    simp only [map_add, hs2, Subfield.coe_add]
  obtain ⟨u, hu, hsu⟩ := H (σf a + σf b) (σf (a + b)) (hs1 _) hst
  rw [hr, hs1, hs1] at hsu
  have hmem : (p : R) ∣ (σf a + σf b - σf (a + b)) * u := by
    rw [← hsu]
    exact ⟨σf a * σf b * r, by ring⟩
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h2 : (p : R) ∣ σf a + σf b - σf (a + b) := by
    have h := hmem.mul_right w
    rwa [mul_assoc, hw, mul_one] at h
  rw [Ideal.mem_span_singleton]
  have heq : σf (a + b) - σf a - σf b = -(σf a + σf b - σf (a + b)) := by ring
  rw [heq]
  exact (dvd_neg).mpr h2

end GlobalTheory.CompanionTheory.Ar.GR
