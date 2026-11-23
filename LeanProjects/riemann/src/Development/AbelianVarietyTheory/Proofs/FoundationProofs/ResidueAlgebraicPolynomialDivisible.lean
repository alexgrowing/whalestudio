import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory.K5

theorem exists_int_poly_root_mod_p : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (v : Valuation Ωl ℝ≥0), (∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) → v (p : Ωl) < 1 → ∀ (y : Ωl) (b : O0 p), IsAlgebraic ℤ y → v y ≤ 1 → v (y - algebraMap (O0 p) Ωl b) < 1 → ∃ P : ℤ[X], P.map (Int.castRingHom (ZMod p)) ≠ 0 ∧ (p : O0 p) ∣ aeval b P := by
  intro p hpf Ωl _ _ hC v hv _ y b hy hyv hyb
  haveI : CharZero Ωl := Basic.charZero_of_isClo hC
  obtain ⟨P0, hP0, hP0y⟩ := hy
  have hprim : P0.primPart.IsPrimitive := Polynomial.isPrimitive_primPart P0
  have hPy : aeval y P0.primPart = 0 := by
    have e := P0.eq_C_content_mul_primPart
    have hc : P0.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
    rw [e, map_mul, aeval_C] at hP0y
    rcases mul_eq_zero.1 hP0y with h | h
    · exact absurd (by simpa using h) hc
    · exact h
  refine ⟨P0.primPart, ?_, ?_⟩
  · intro h0
    have hd : ∀ n, (p : ℤ) ∣ P0.primPart.coeff n := by
      intro n
      have := congrArg (fun Q => Q.coeff n) h0
      simp only [coeff_map, coeff_zero, eq_intCast] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
    have hu := hprim (p : ℤ) ((Polynomial.C_dvd_iff_dvd_coeff _ _).2 hd)
    have := Int.isUnit_iff.1 hu
    have h2 := hpf.out.two_le
    omega
  · set P := P0.primPart
    set b' := algebraMap (O0 p) Ωl b
    have hb' : v b' ≤ 1 := (hv b').2 isIntegral_algebraMap
    let yi : v.integer := ⟨y, hyv⟩
    let bi : v.integer := ⟨b', hb'⟩
    obtain ⟨d, hd⟩ := Polynomial.sub_dvd_eval_sub yi bi (P.map (Int.castRingHom v.integer))
    have hev : ∀ z : v.integer, v.integer.subtype ((P.map (Int.castRingHom v.integer)).eval z) = aeval (z : Ωl) P := by
      intro z
      rw [Polynomial.eval_map, aeval_def]
      have := Polynomial.hom_eval₂ P (Int.castRingHom v.integer) v.integer.subtype z
      rw [show v.integer.subtype.comp (Int.castRingHom v.integer) = algebraMap ℤ Ωl from RingHom.ext_int _ _] at this
      exact this
    have hd' := congrArg v.integer.subtype hd
    rw [map_sub, map_mul, map_sub, hev, hev] at hd'
    have hd'' : aeval y P - aeval b' P = (y - b') * (d : Ωl) := hd'
    have hkey : aeval b' P = -((y - b') * (d : Ωl)) := by
      rw [← hd'', hPy]; ring
    have hmap : algebraMap (O0 p) Ωl (aeval b P) = aeval b' P := by
      rw [aeval_def, aeval_def, Polynomial.hom_eval₂]
      congr 1
      exact RingHom.ext_int _ _
    have hlt : v (algebraMap (O0 p) Ωl (aeval b P)) < 1 := by
      rw [hmap, hkey, Valuation.map_neg, Valuation.map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' hyb d.2
    obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
    have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
    have hnu : ¬ IsUnit (aeval b P) := by
      rintro ⟨u, hu⟩
      have h1 : v (algebraMap (O0 p) Ωl (u⁻¹ : (O0 p)ˣ)) ≤ 1 := (hv _).2 isIntegral_algebraMap
      have h2 : v (algebraMap (O0 p) Ωl (aeval b P)) * v (algebraMap (O0 p) Ωl (u⁻¹ : (O0 p)ˣ)) = 1 := by
        rw [← Valuation.map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, Valuation.map_one]
      have h3 : v (algebraMap (O0 p) Ωl (aeval b P)) * v (algebraMap (O0 p) Ωl (u⁻¹ : (O0 p)ˣ)) < 1 :=
        mul_lt_one_of_nonneg_of_lt_one_left zero_le' hlt h1
      rw [h2] at h3
      exact lt_irrefl _ h3
    have hm : aeval b P ∈ IsLocalRing.maximalIdeal (O0 p) := hnu
    rw [hmax, Ideal.mem_span_singleton] at hm
    exact hm

end GlobalTheory.K5
