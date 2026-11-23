import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exists_eq_exp_of_rat {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (hε : Function.Injective ε) (x : ℚ) :
    ∃ a : Ω, ε a = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  set n := x.den with hn
  have hn0 : 0 < n := x.den_pos
  haveI : NeZero n := ⟨hn0.ne'⟩
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn0.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (Polynomial.degree_cyclotomic_pos n Ω hn0).ne'
  have hp : IsPrimitiveRoot ζ n := (Polynomial.isRoot_cyclotomic_iff).mp hζ
  have hp' : IsPrimitiveRoot (ε ζ) n := hp.map_of_injective hε
  have hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ n = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have h := Rat.mul_den_eq_num x
    have h' : ((x : ℂ) * (n : ℂ)) = (x.num : ℂ) := by exact_mod_cast h
    rw [← h']; ring
  obtain ⟨i, -, hi⟩ := hp'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem eOm_spec {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (hε : Function.Injective ε) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exists_eq_exp_of_rat ε hε x)

theorem eOm_props : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Function.Injective ε → (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ k : ℤ, eOm ε (k : ℚ) = 1) ∧ (∀ x : ℚ, eOm ε x = 1 → ∃ k : ℤ, x = k) := by
  intro Ω _ _ _ ε hε
  refine ⟨eOm_spec ε hε, ?_, ?_, ?_⟩
  · intro x y
    apply hε
    rw [map_mul, eOm_spec ε hε, eOm_spec ε hε, eOm_spec ε hε, ← Complex.exp_add]
    congr 1; push_cast; ring
  · intro k
    apply hε
    rw [map_one, eOm_spec ε hε, Complex.exp_eq_one_iff]
    exact ⟨k, by push_cast; ring⟩
  · intro x hx
    have h := eOm_spec ε hε x
    rw [hx, map_one] at h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h.symm
    refine ⟨k, ?_⟩
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (x : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ hne
      rw [hk]; ring
    exact_mod_cast this

end GlobalTheory.KZ
