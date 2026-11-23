import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffNormLeOne

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

private theorem norm_le_one_of_isIntegral_zl (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_mem_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (a : c.O) :
    ‖(a : PadicAlgCl l)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_zl l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map c.O.val)

theorem norm_unit_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (u : c.Oˣ) :
    ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := norm_le_one_of_mem_coefO c u
  have h3 := norm_le_one_of_mem_coefO c (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  nlinarith

theorem mem_coefO_of_memE_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : Qbar l),
    MemE c x → ‖x‖ ≤ 1 → x ∈ c.O := by
  intro l _ c x hE hx
  obtain ⟨k, hk⟩ := hE
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simpa using hk
  set y : c.O := ⟨_, hk⟩ with hy
  set L : c.O := (l : c.O) ^ k with hL
  have hLval : ((L : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) ^ k := by simp [hL]
  have hl0 : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hL0 : L ≠ 0 := by
    intro h
    have : ((L : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    rw [hLval] at this
    exact pow_ne_zero k hl0 this
  have hnl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  by_cases hy0 : y = 0
  · have : (l : PadicAlgCl l) ^ k * x = 0 := by
      have := congrArg (fun z : c.O => (z : PadicAlgCl l)) hy0
      simpa [hy] using this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (pow_ne_zero k hl0)
    · rw [h]; exact c.O.zero_mem
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have key : ∀ z : c.O, z ≠ 0 → ∃ n : ℕ, ‖(z : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ n ∧
      ϖ ^ n ∣ z ∧ z ∣ ϖ ^ n := by
    intro z hz
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
    refine ⟨n, ?_, ?_, ?_⟩
    · rw [h, Subalgebra.coe_mul, norm_mul, norm_unit_coefO, one_mul, Subalgebra.coe_pow, norm_pow]
    · exact ⟨(u : c.O), by rw [h, mul_comm]⟩
    · exact ⟨((u⁻¹ : c.Oˣ) : c.O), by rw [h, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩
  obtain ⟨a, hya, hdy, -⟩ := key y hy0
  obtain ⟨b, hLb, -, hdL⟩ := key L hL0
  have hϖ1 : ‖(ϖ : PadicAlgCl l)‖ ≤ 1 := norm_le_one_of_mem_coefO c ϖ
  have hϖ0 : 0 < ‖(ϖ : PadicAlgCl l)‖ := by
    rw [norm_pos_iff]
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hlt1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hyx : ((y : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) ^ k * x := rfl
  have hLlt : ‖((L : c.O) : PadicAlgCl l)‖ < 1 := by
    rw [hLval, norm_pow, hnl]
    exact pow_lt_one₀ (by positivity) hlt1 (by omega)
  have hϖlt : ‖(ϖ : PadicAlgCl l)‖ < 1 := by
    rcases lt_or_eq_of_le hϖ1 with h | h
    · exact h
    exfalso
    rw [hLb, h, one_pow] at hLlt
    exact lt_irrefl _ hLlt
  have hab : b ≤ a := by
    have hle : ‖(ϖ : PadicAlgCl l)‖ ^ a ≤ ‖(ϖ : PadicAlgCl l)‖ ^ b := by
      rw [← hya, ← hLb, hyx, hLval, norm_mul]
      calc ‖(l : PadicAlgCl l) ^ k‖ * ‖x‖ ≤ ‖(l : PadicAlgCl l) ^ k‖ * 1 :=
            mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ = _ := mul_one _
    exact (pow_le_pow_iff_right_of_lt_one₀ hϖ0 hϖlt).1 hle
  have hdiv : L ∣ y := dvd_trans hdL (dvd_trans (pow_dvd_pow ϖ hab) hdy)
  obtain ⟨z, hz⟩ := hdiv
  have : (l : PadicAlgCl l) ^ k * x = (l : PadicAlgCl l) ^ k * (z : PadicAlgCl l) := by
    rw [← hyx, hz, Subalgebra.coe_mul, hLval]
  rw [mul_left_cancel₀ (pow_ne_zero k hl0) this]
  exact z.2

end GlobalTheory.Ord2
