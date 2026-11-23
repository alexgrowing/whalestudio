import Mathlib

theorem UpperTheory.exists_residue_map_padicAlgCl_integers :
    ∀ (l : ℕ) [Fact l.Prime], ∃ (k : Type) (_ : Field k) (_ : CharP k l) (A : Subring (PadicAlgCl l)) (red : A →+* k), (∀ x : PadicAlgCl l, x ∈ A ↔ ‖x‖ ≤ 1) ∧ ∀ x : A, red x = 0 ↔ ‖(x : PadicAlgCl l)‖ < 1 := by
  intro l _
  have hna : ∀ x y : PadicAlgCl l, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := fun x y =>
    IsUltrametricDist.norm_add_le_max x y
  let A : Subring (PadicAlgCl l) :=
    { carrier := {x | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, norm_mul] at *
        exact mul_le_one₀ ha (norm_nonneg _) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => (hna a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using ha }
  have hA : ∀ x : PadicAlgCl l, x ∈ A ↔ ‖x‖ ≤ 1 := fun x => Iff.rfl
  let I : Ideal A :=
    { carrier := {x | ‖(x : PadicAlgCl l)‖ < 1}
      add_mem' := fun {a b} ha hb => lt_of_le_of_lt (hna _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        show ‖((c * x : A) : PadicAlgCl l)‖ < 1
        rw [Subring.coe_mul, norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) c.2) hx }
  have hI : ∀ x : A, x ∈ I ↔ ‖(x : PadicAlgCl l)‖ < 1 := fun x => Iff.rfl
  have hmax : I.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨by simp [hI], fun J x hIJ hx hxJ => ?_⟩
    rw [hI, not_lt] at hx
    have h1 : ‖(x : PadicAlgCl l)‖ = 1 := le_antisymm x.2 hx
    have hx0 : (x : PadicAlgCl l) ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : PadicAlgCl l)⁻¹ ∈ A := by
      rw [hA, norm_inv, h1, inv_one]
    have : (⟨_, hinv⟩ : A) * x = 1 := Subtype.ext (inv_mul_cancel₀ hx0)
    rw [← this]
    exact J.mul_mem_left _ hxJ
  haveI := hmax
  have hl : ‖((l : A) : PadicAlgCl l)‖ < 1 := by
    have h := congrArg NNReal.toReal (PadicAlgCl.valuation_p l)
    rw [PadicAlgCl.valuation_coe] at h
    push_cast
    rw [h]
    have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    simp only [one_div, NNReal.coe_inv, NNReal.coe_natCast]
    exact inv_lt_one_of_one_lt₀ hl1
  refine ⟨A ⧸ I, Ideal.Quotient.field I, ?_, A, Ideal.Quotient.mk I, hA, fun x => ?_⟩
  · rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact hl
  · rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hI x
