import Mathlib

open scoped NNReal

private theorem UpperTheory.Reformulated.B.NormOnValuationRing.norm_algebraMap {l : ℕ} [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  exact PadicAlgCl.norm_extends l (a : ℚ_[l])

private theorem UpperTheory.Reformulated.B.NormOnValuationRing.norm_le_one {l : ℕ} [Fact (Nat.Prime l)] {y : PadicAlgCl l}
    (hy : IsIntegral ℤ_[l] y) : ‖y‖ ≤ 1 := by
  let v : Valuation (PadicAlgCl l) ℝ≥0 := NormedField.valuation
  have hv : ∀ z : PadicAlgCl l, z ∈ v.integer ↔ ‖z‖ ≤ 1 := fun z => by
    rw [Valuation.mem_integer_iff]
    exact NNReal.coe_le_coe.symm
  let f : ℤ_[l] →+* v.integer :=
    (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer fun a => (hv _).2 (by
      rw [UpperTheory.Reformulated.B.NormOnValuationRing.norm_algebraMap]; exact a.norm_le_one)
  have h : IsIntegral v.integer y :=
    hy.map_of_comp_eq f (RingHom.id _) (by ext a; rfl)
  exact (hv y).1 ((Valuation.integer.integers v).mem_of_integral h)

theorem UpperTheory.Reformulated.B.NormOnValuationRing.mem_max_iff :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {T : Type}
    [inst_1 : CommRing T] [inst_2 : IsLocalRing T] [inst_3 : Algebra ℤ_[l] T] [Algebra.IsIntegral ℤ_[l] T]
    (φ : T →ₐ[ℤ_[l]] PadicAlgCl l) (x : T), x ∈ IsLocalRing.maximalIdeal T ↔ ‖(φ : T → PadicAlgCl l) x‖ < (1 : ℝ) := by
  intro l _ T _ _ _ _ φ x
  have hle : ∀ t : T, ‖φ t‖ ≤ 1 := fun t =>
    UpperTheory.Reformulated.B.NormOnValuationRing.norm_le_one ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) t).map φ)
  let P : Ideal T :=
    { carrier := {t | ‖φ t‖ < 1}
      add_mem' := fun {a b} ha hb => by
        change ‖φ (a + b)‖ < 1
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        change ‖φ (c * a)‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) ha }
  have hP : ∀ t : T, t ∈ P ↔ ‖φ t‖ < 1 := fun _ => Iff.rfl
  have hprime : P.IsPrime := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · rw [Ideal.ne_top_iff_one, hP]
      simp
    · rw [hP, map_mul, norm_mul] at hab
      by_contra h
      rw [not_or, hP, hP, not_lt, not_lt] at h
      exact absurd (one_le_mul_of_one_le_of_one_le h.1 h.2) (not_le.2 hab)
  have hcomap : P.comap (algebraMap ℤ_[l] T) = IsLocalRing.maximalIdeal ℤ_[l] := by
    ext a
    rw [Ideal.mem_comap, hP, φ.commutes, UpperTheory.Reformulated.B.NormOnValuationRing.norm_algebraMap,
      IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  have hmax : P.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) P
      (hcomap ▸ IsLocalRing.maximalIdeal.isMaximal ℤ_[l])
  rw [← IsLocalRing.eq_maximalIdeal hmax, hP]
