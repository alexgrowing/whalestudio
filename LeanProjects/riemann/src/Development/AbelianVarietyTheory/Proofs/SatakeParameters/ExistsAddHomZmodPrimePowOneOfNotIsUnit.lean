import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong

namespace GlobalTheory

theorem natCast_dvd_of_pow_dvd_of_not_isUnit (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    (l : ℕ) (hl : l.Prime) (hu : ¬ IsUnit (l : R)) :
    ∀ (m k : ℕ), (l : R) ^ m ∣ (k : R) → l ^ m ∣ k := by
  intro m
  induction m with
  | zero => intro k _; simp
  | succ m ih =>
    intro k hk
    have h1 : (l : R) ∣ (k : R) := (dvd_pow_self _ (Nat.succ_ne_zero m)).trans hk
    have h2 : l ∣ k := by
      by_contra hnd
      have hcop : Nat.Coprime l k := (Nat.Prime.coprime_iff_not_dvd hl).2 hnd
      have hg := Nat.gcd_eq_gcd_ab l k
      rw [hcop] at hg
      apply hu
      obtain ⟨c, hc⟩ := h1
      refine isUnit_of_dvd_one ⟨(Nat.gcdA l k : R) + (Nat.gcdB l k : R) * c, ?_⟩
      have := congrArg (fun z : ℤ => (z : R)) hg
      simp only [Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast] at this
      rw [this, hc]; ring
    obtain ⟨k', rfl⟩ := h2
    have hl0 : (l : R) ≠ 0 := by exact_mod_cast hl.ne_zero
    have hk' : (l : R) ^ m ∣ (k' : R) := by
      obtain ⟨c, hc⟩ := hk
      refine ⟨c, ?_⟩
      apply mul_left_cancel₀ hl0
      rw [Nat.cast_mul] at hc
      rw [hc]; ring
    rw [pow_succ, mul_comm]
    exact mul_dvd_mul_left l (ih k' hk')

theorem exists_addHom_zmod_pow_one_of_not_isUnit :
    ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (l m : ℕ), l.Prime → ¬ IsUnit (l : R) →
      ∃ φ : R →+ ZMod (l ^ m), φ 1 = 1 ∧ ∀ x, φ ((l : R) ^ m * x) = 0 := by
  intro R _ _ _ l m hl hu
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  set I : Ideal R := Ideal.span {(l : R) ^ m} with hI
  have hlI : (((l ^ m : ℕ) : ℤ) : R ⧸ I) = 0 := by
    rw [Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem,
      hI, Nat.cast_pow]
    exact Ideal.subset_span rfl
  let f : ZMod (l ^ m) →+ R ⧸ I := ZMod.lift (l ^ m) ⟨Int.castAddHom (R ⧸ I), by
    simpa using hlI⟩
  have hf_nat : ∀ k : ℕ, f (k : ZMod (l ^ m)) = (k : R ⧸ I) := by
    intro k
    have := ZMod.lift_coe (l ^ m) ⟨Int.castAddHom (R ⧸ I), by simpa using hlI⟩ (k : ℤ)
    simpa using this
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [← ZMod.natCast_zmod_val x, hf_nat, ← map_natCast (Ideal.Quotient.mk I),
      Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton] at hx
    have hd := natCast_dvd_of_pow_dvd_of_not_isUnit R l hl hu m _ hx
    have hlt := ZMod.val_lt x
    have h0 : x.val = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    rw [← ZMod.natCast_zmod_val x, h0, Nat.cast_zero]
  obtain ⟨Λ, hΛ⟩ := (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
    f hinj (ZMod.toAddCircle (N := l ^ m))
  have hΛ' : ∀ z, Λ (f z) = ZMod.toAddCircle z := fun z => DFunLike.congr_fun hΛ z
  have htor : ∀ q : R ⧸ I, ∃ k : ZMod (l ^ m), ZMod.toAddCircle k = Λ q := by
    intro q
    have h0 : (l ^ m) • Λ q = 0 := by
      rw [← map_nsmul]
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I), ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2, map_zero]
      rw [hI, Ideal.mem_span_singleton, Nat.cast_pow]
      exact dvd_mul_right _ _
    obtain ⟨k, -, hk⟩ := (AddCircle.nsmul_eq_zero_iff (pow_pos hl.pos _)).1 h0
    refine ⟨k, ?_⟩
    rw [ZMod.toAddCircle_natCast, ← hk, mul_one]
  choose a ha using htor
  let A : R ⧸ I →+ ZMod (l ^ m) := AddMonoidHom.mk' a (by
    intro x y
    apply ZMod.toAddCircle_injective
    rw [map_add, ha, ha, ha, map_add])
  refine ⟨A.comp (Ideal.Quotient.mk I).toAddMonoidHom, ?_, ?_⟩
  · show a (Ideal.Quotient.mk I 1) = 1
    apply ZMod.toAddCircle_injective
    rw [ha, map_one]
    have := hΛ' 1
    rw [show (1 : ZMod (l ^ m)) = ((1 : ℕ) : ZMod (l ^ m)) by simp, hf_nat] at this
    simpa using this
  · intro x
    show a (Ideal.Quotient.mk I ((l : R) ^ m * x)) = 0
    have hmem : (l : R) ^ m * x ∈ I := by
      rw [hI]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hmem]
    apply ZMod.toAddCircle_injective
    rw [ha, map_zero, map_zero]

end GlobalTheory
