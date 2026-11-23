import Mathlib

open Polynomial

namespace GlobalTheory.ResiduePowerFixed

theorem pow_fixed_of_algebraic (l : ℕ) [Fact (Nat.Prime l)] {k : Type} [Field k]
    [Algebra (ZMod l) k] (y : k) (hy : IsAlgebraic (ZMod l) y) :
    ∃ N : ℕ, 0 < N ∧ y ^ l ^ N = y := by
  let F := IntermediateField.adjoin (ZMod l) {y}
  haveI : FiniteDimensional (ZMod l) F := IntermediateField.adjoin.finiteDimensional hy.isIntegral
  haveI : Finite F := Module.finite_of_finite (ZMod l)
  letI := Fintype.ofFinite F
  haveI : CharP F l := charP_of_injective_algebraMap (algebraMap (ZMod l) F).injective l
  obtain ⟨n, -, hcard⟩ := FiniteField.card F l
  refine ⟨n, n.pos, ?_⟩
  have h := FiniteField.pow_card (⟨y, IntermediateField.mem_adjoin_simple_self _ y⟩ : F)
  rw [hcard] at h
  simpa using congrArg Subtype.val h

theorem exists_primitive {Ω : Type} [Field Ω] [Algebra ℚ Ω] (x : Ω) (hx : IsAlgebraic ℚ x) :
    ∃ p : ℤ[X], p.IsPrimitive ∧ aeval x p = 0 := by
  have hx' : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr hx
  obtain ⟨p, hp0, hp⟩ := hx'
  refine ⟨p.primPart, p.isPrimitive_primPart, ?_⟩
  have hc : algebraMap ℤ Ω p.content ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ Ω]
    refine (_root_.map_ne_zero _).mpr ?_
    have : p.content ≠ 0 := Polynomial.content_eq_zero_iff.not.mpr hp0
    rw [algebraMap_int_eq, eq_intCast]
    exact_mod_cast this
  rw [Polynomial.eq_C_content_mul_primPart p, map_mul, aeval_C] at hp
  exact (mul_eq_zero.mp hp).resolve_left hc

theorem residue_pow_fixed (l : ℕ) [Fact (Nat.Prime l)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hl : A.valuation (l : Ω) < 1) (xA : A) :
    ∃ N : ℕ, 0 < N ∧ IsLocalRing.residue A xA ^ l ^ N = IsLocalRing.residue A xA := by
  classical

  have hlm : (l : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    simpa using hl
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  haveI hchar : CharP (IsLocalRing.ResidueField A) l := by
    obtain ⟨q, hq⟩ := CharP.exists (IsLocalRing.ResidueField A)
    haveI := hq
    have hdvd : q ∣ l := (CharP.cast_eq_zero_iff _ q l).mp hl0
    rcases (Fact.out : l.Prime).eq_one_or_self_of_dvd q hdvd with h1 | h1
    · exfalso
      subst h1
      have h := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) 1 1).mpr dvd_rfl
      have h' : (1 : IsLocalRing.ResidueField A) = 0 := by
        rw [← Nat.cast_one]
        exact h
      exact one_ne_zero h'
    · subst h1
      exact hq
  letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l
  apply pow_fixed_of_algebraic l

  have hxalg : IsAlgebraic ℚ (xA : Ω) := Algebra.IsAlgebraic.isAlgebraic _
  obtain ⟨p, hprim, hp⟩ := exists_primitive (xA : Ω) hxalg
  refine ⟨p.map (Int.castRingHom (ZMod l)), ?_, ?_⟩
  · intro h0
    have hdvd : ∀ n, (l : ℤ) ∣ p.coeff n := fun n => by
      have h := congrArg (fun q => Polynomial.coeff q n) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp h
    have hC : Polynomial.C (l : ℤ) ∣ p := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd
    have hcont := Polynomial.dvd_content_iff_C_dvd.mpr hC
    rw [hprim.content_eq_one] at hcont
    have h1 := Int.eq_one_of_dvd_one (by positivity) hcont
    exact (Fact.out : l.Prime).one_lt.ne' (by exact_mod_cast h1)
  · have hA : aeval xA p = 0 := by
      have h := Polynomial.aeval_algHom_apply (A.subtype.toIntAlgHom) xA p
      have h2 : A.subtype.toIntAlgHom (aeval xA p) = 0 := by
        rw [← h]
        exact hp
      exact Subtype.ext h2
    have e : aeval (IsLocalRing.residue A xA) (p.map (Int.castRingHom (ZMod l))) =
        aeval (IsLocalRing.residue A xA) p := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map]
      congr 1
      exact RingHom.ext_int _ _
    rw [e]
    rw [show IsLocalRing.residue A xA = (IsLocalRing.residue A).toIntAlgHom xA from rfl,
      Polynomial.aeval_algHom_apply, hA, map_zero]

end GlobalTheory.ResiduePowerFixed
