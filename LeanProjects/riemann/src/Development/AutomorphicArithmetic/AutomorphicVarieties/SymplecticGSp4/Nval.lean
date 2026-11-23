import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.nval :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l), IsNVal c.O (PadicAlgCl l) fun x => -Real.log ‖x‖ * ((eO l c.O).toNat : ℝ) / Real.log l := by
  intro l _ c
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hL : 0 < Real.log l := Real.log_pos hl
  have he : (0 : ℝ) ≤ ((eO l c.O).toNat : ℝ) := Nat.cast_nonneg _
  have anti : ∀ a b : PadicAlgCl l, a ≠ 0 → ‖a‖ ≤ ‖b‖ →
      -Real.log ‖b‖ * ((eO l c.O).toNat : ℝ) / Real.log l ≤
        -Real.log ‖a‖ * ((eO l c.O).toNat : ℝ) / Real.log l := by
    intro a b ha hab
    have hlog : Real.log ‖a‖ ≤ Real.log ‖b‖ := Real.log_le_log (norm_pos_iff.mpr ha) hab
    apply div_le_div_of_nonneg_right _ hL.le
    exact mul_le_mul_of_nonneg_right (by linarith) he
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)]
    ring
  · intro x y hx hy hxy
    have h := IsUltrametricDist.norm_add_le_max x y
    rcases le_total ‖x‖ ‖y‖ with h1 | h1
    · rw [max_eq_right h1] at h
      exact (min_le_right _ _).trans (anti _ _ hxy h)
    · rw [max_eq_left h1] at h
      exact (min_le_left _ _).trans (anti _ _ hxy h)
  · intro a ha
    have h := normO l c.O a ha
    have h2 := congrArg Real.log h
    rw [Real.log_pow, Real.log_pow, Real.log_inv] at h2
    show -Real.log ‖(a : PadicAlgCl l)‖ * ((eO l c.O).toNat : ℝ) / Real.log l = _
    field_simp
    linarith
