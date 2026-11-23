import Mathlib

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.CmOK :
    ℕ → ℤ → ℤ → ℕ → Prop :=
    fun (a : ℕ) (b c : ℤ) (d : ℕ) ↦
      (4 : ℤ) * (↑a : ℤ) * c = b ^ (2 : ℕ) + (↑d : ℤ) ∧ Odd a ∧ d % (8 : ℕ) = (7 : ℕ) ∧ Nat.Prime d

noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta :
    ℤ → ℕ → ℂ :=
    fun (b : ℤ) (d : ℕ) ↦ ((↑b : ℂ) + Complex.I * (↑√(↑d : ℝ) : ℂ)) / (2 : ℂ)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.KF :
    ℤ → ℕ → IntermediateField ℚ ℂ :=
    fun (b : ℤ) (d : ℕ) ↦ ℚ⟮UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d⟯

private theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq (b : ℤ) (d : ℕ) :
    UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d =
      (b : ℂ) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d - ((b : ℂ) ^ 2 + (d : ℂ)) / 4 := by
  have h : ((√(d : ℝ) : ℝ) : ℂ) * ((√(d : ℝ) : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    simp
  unfold UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta
  linear_combination (((√(d : ℝ) : ℝ) : ℂ) * ((√(d : ℝ) : ℝ) : ℂ) / 4) * Complex.I_mul_I - (1 / 4 : ℂ) * h

private theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_integral (b : ℤ) (d : ℕ) :
    IsIntegral ℚ (UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (b : ℚ) * Polynomial.X
    + Polynomial.C (((b : ℚ) ^ 2 + (d : ℚ)) / 4), ?_, ?_⟩
  · monicity!
  · have h := UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq b d
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, eq_ratCast]
    push_cast
    linear_combination h

theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.kap_repr :
    ∀ {a : ℕ} {b c : ℤ} {d : ℕ},
      UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.CmOK a b c d →
        ∀ {x : ℂ}, x ∈ UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.KF b d → ∃ (u : ℚ) (v : ℚ), x = (↑u : ℂ) + (↑v : ℂ) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d := by
  intro a b c d _ x hx
  have hx' : x ∈ Algebra.adjoin ℚ {UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_integral b d).isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by simp [hy]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    refine ⟨u * u' - v * v' * (((b : ℚ) ^ 2 + (d : ℚ)) / 4), u * v' + v * u' + v * v' * b, ?_⟩
    push_cast
    linear_combination ((v : ℂ) * (v' : ℂ)) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq b d
