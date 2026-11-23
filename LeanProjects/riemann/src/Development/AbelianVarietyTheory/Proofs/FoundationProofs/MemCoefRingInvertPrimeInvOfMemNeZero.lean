import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallNormLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

theorem memE_inv_of_mem : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (d : Qbar l), d ∈ c.O → d ≠ 0 → MemE c d⁻¹ := by
  intro l _ c d hd hd0
  set x : c.O := ⟨d, hd⟩ with hxdef
  have hx0 : x ≠ 0 := fun h => hd0 (congrArg Subtype.val h)
  set L : c.O := ((l : ℕ) : c.O) with hLdef
  have hLval : (L : Qbar l) = ((l : ℕ) : Qbar l) := by simp [hLdef]
  have hL0 : L ≠ 0 := by
    intro h
    have : ((l : ℕ) : Qbar l) = 0 := by rw [← hLval, h]; rfl
    have h1 := (norm_natCast_l (l := l))
    rw [this, norm_zero] at h1
    have : (0:ℝ) < (l:ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)
    linarith
  have hLnu : ¬ IsUnit L := by
    rintro ⟨u, hu⟩
    have h1 : ((u : c.O) : Qbar l) * ((u⁻¹ : c.Oˣ) : c.O) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
    have hn2 : ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ ≤ 1 := norm_le_one_of_mem_coef c (SetLike.coe_mem _)
    have hu' : ((u : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := by rw [hu, hLval]
    rw [hu'] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have h3 := norm_natCast_l_lt_one (l := l)
    have h4 : ‖((l : ℕ) : Qbar l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hn2) h3
    linarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨v, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨m, u', hLu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hL0 hϖ
  have hm : m ≠ 0 := by
    rintro rfl
    apply hLnu
    rw [hLu, pow_zero, mul_one]; exact u'.isUnit
  have hϖL : ϖ ∣ L := by
    rw [hLu]
    exact Dvd.dvd.mul_left (dvd_pow_self ϖ hm) _
  have hdiv : x ∣ L ^ v := by
    rw [hxu]
    exact (Units.mul_left_dvd).2 (pow_dvd_pow_of_dvd hϖL v)
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨v, ?_⟩
  have hq' : ((l : ℕ) : Qbar l) ^ v = d * (q : Qbar l) := by
    have := congrArg (fun y : c.O => (y : Qbar l)) hq
    simpa [hLval, hxdef] using this
  rw [hq', mul_comm d, mul_assoc, mul_inv_cancel₀ hd0, mul_one]
  exact q.2

end GlobalTheory.Ord2

end
