import Mathlib

theorem UpperTheory.Reformulated.B.NormLeOneOfIntegral.norm_le_one_of_int :
    ∀ {A K : Type} [inst : CommRing A]
    [inst_1 : NormedField K] [IsUltrametricDist K] [inst_3 : Algebra A K],
    (∀ (a : A), ‖(Algebra.algebraMap A K : A → K) a‖ ≤ (1 : ℝ)) → ∀ {x : K}, IsIntegral A x → ‖x‖ ≤ (1 : ℝ) := by
  intro A K _ _ _ _ h x hx
  let v : Valuation K NNReal := NormedField.valuation
  have hv : ∀ y : K, v y ≤ 1 ↔ ‖y‖ ≤ 1 := fun y => by
    change ‖y‖₊ ≤ 1 ↔ ‖y‖ ≤ 1
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  let f : A →+* v.integer :=
    (algebraMap A K).codRestrict v.integer (fun a => (hv _).2 (h a))
  have hx' : IsIntegral v.integer x :=
    IsIntegral.map_of_comp_eq f (RingHom.id K) (by ext a; rfl) hx
  exact (hv x).1 ((Valuation.integer.integers v).mem_of_integral hx')
