import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.NChart

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base
open ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S MeasureTheory

section Generic
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  {F : ℕ → Submodule ℝ A} {L : ℕ} {st : A →ₗ[ℝ] A}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem haar_of_equiv [MeasurableSpace A] [BorelSpace A] [MeasurableSpace E] [BorelSpace E]
    (hF : IsFil F L) (hst : IsAdj F st) (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃ₗ[ℝ] lieN F st) :
    SigmaFinite (μ.map fun x => NormedSpace.exp (e x : A)) ∧
      (μ.map fun x => NormedSpace.exp (e x : A)) ≠ 0 ∧
      (μ.map fun x => NormedSpace.exp (e x : A)) {x | x ∉ grpN F st} = 0 ∧
      ∀ s ∈ grpN F st, (μ.map fun x => NormedSpace.exp (e x : A)).map (s * ·) =
        μ.map fun x => NormedSpace.exp (e x : A) := by
  let e' := e.toContinuousLinearEquiv
  have : (Measure.map e' μ).IsAddHaarMeasure := e'.isAddHaarMeasure_map μ
  have h := exp_chart_haar hF hst (Measure.map e' μ)
  have he := exp_chart_embedding (st := st) hF
  simp only [] at h
  rw [Measure.map_map he.measurable e'.continuous.measurable] at h
  exact h

omit [FiniteDimensional ℝ A] in
theorem growth_of_equiv (hF : IsFil F L) (U0 : E ≃ₗ[ℝ] A) : ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ Y ∈ F 0,
    ‖U0.symm Y‖ ≤ C * ‖U0.symm (NormedSpace.exp Y - 1)‖ *
      (1 + ‖U0.symm (NormedSpace.exp Y - 1)‖) ^ M := by
  obtain ⟨C, M, hC, h⟩ := hF.log_growth
  let U := U0.toContinuousLinearEquiv
  set a := ‖(U.symm : A →L[ℝ] E)‖ with ha
  set b := ‖(U : E →L[ℝ] A)‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have h1 : ∀ X, ‖U0.symm X‖ ≤ a * ‖X‖ := fun X => (U.symm : A →L[ℝ] E).le_opNorm X
  have h2 : ∀ X, ‖X‖ ≤ b * ‖U0.symm X‖ := fun X => by
    have := (U : E →L[ℝ] A).le_opNorm (U.symm X)
    rwa [ContinuousLinearEquiv.coe_coe, U.apply_symm_apply] at this
  refine ⟨a * C * b * (1 + b) ^ M, M, by positivity, fun Y hY => ?_⟩
  set s := ‖U0.symm (NormedSpace.exp Y - 1)‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg _
  have h3 := h2 (NormedSpace.exp Y - 1)
  have h4 : 1 + ‖NormedSpace.exp Y - 1‖ ≤ (1 + b) * (1 + s) := by nlinarith
  calc ‖U0.symm Y‖ ≤ a * ‖Y‖ := h1 Y
    _ ≤ a * (C * ‖NormedSpace.exp Y - 1‖ * (1 + ‖NormedSpace.exp Y - 1‖) ^ M) :=
        mul_le_mul_of_nonneg_left (h Y hY) ha0
    _ ≤ a * (C * (b * s) * ((1 + b) * (1 + s)) ^ M) := by gcongr
    _ = _ := by rw [mul_pow]; ring

end Generic

open scoped Matrix.Norms.Operator

noncomputable def unrealL (m : ℕ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) ≃ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun := unrealify
  invFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' x y := by ext i j; apply Complex.ext <;> simp [unrealify]
  map_smul' c x := by ext i j; apply Complex.ext <;> simp [unrealify]
  left_inv x := by
    ext ⟨i, j, b⟩
    cases b <;> simp [unrealify, realifyFun]
  right_inv X := by ext i j; apply Complex.ext <;> simp [unrealify, realifyFun]

theorem sqrt_hs {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    Real.sqrt (S7.hs X) = ‖(unrealL m).symm X‖ := by
  rw [EuclideanSpace.norm_eq, S7.hs]
  congr 1
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show ‖X i j‖ ^ 2 = ‖(X i j).im‖ ^ 2 + ‖(X i j).re‖ ^ 2
  rw [Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

variable {k r : ℕ}

theorem lieE_eq : lieE (Nset k r) =
    (lieN (levF (levB k r)) (adjH (Hpk k r))).map (unrealL _).symm.toLinearMap := by
  rw [lieE, lieOf_Nset_eq, ← Submodule.span_eq (Submodule.map _ _)]
  rfl

theorem unipotent_exp_haar_sqrt_bound (k r : ℕ) :
    (∀ Y ∈ lieOf (Nset k r), ∀ Y' ∈ lieOf (Nset k r),
      NormedSpace.exp Y = NormedSpace.exp Y' → Y = Y') ∧
    (∀ g ∈ Nset k r, ∃ Y ∈ lieOf (Nset k r), NormedSpace.exp Y = g) ∧
    (∀ x : lieE (Nset k r), unrealify (x : EuclideanSpace ℝ _) ∈ lieOf (Nset k r)) ∧
    IsHaarOn (Nset k r) (haarLie (Nset k r) 1) ∧
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ Y ∈ lieOf (Nset k r),
      Real.sqrt (S7.hs Y) ≤ C * Real.sqrt (S7.hs (NormedSpace.exp Y - 1)) *
        (1 + Real.sqrt (S7.hs (NormedSpace.exp Y - 1))) ^ m := by
  have hmem : ∀ x : lieE (Nset k r),
      unrealL _ (x : EuclideanSpace ℝ _) ∈ lieN (levF (levB k r)) (adjH (Hpk k r)) := by
    rintro ⟨x, hx⟩
    rw [lieE_eq] at hx
    obtain ⟨Y, hY, rfl⟩ := hx
    simpa using hY
  refine ⟨fun Y hY Y' hY' h => ?_, fun g hg => ?_, fun x => ?_, ?_, ?_⟩
  · rw [lieOf_Nset_eq] at hY hY'
    exact exp_injOn isFilB (mem_lieN.mp hY).1 (mem_lieN.mp hY').1 h
  · rw [Nset_eq] at hg
    rw [lieOf_Nset_eq]
    exact ⟨_, lg_spec isFilB isAdjB hg⟩
  · rw [lieOf_Nset_eq]; exact hmem x
  · let e : lieE (Nset k r) ≃ₗ[ℝ] lieN (levF (levB k r)) (adjH (Hpk k r)) :=
      { toFun := fun x => ⟨unrealL _ x, hmem x⟩
        invFun := fun Y => ⟨(unrealL _).symm Y, by rw [lieE_eq]; exact ⟨Y, Y.2, rfl⟩⟩
        map_add' := fun x y => Subtype.ext (map_add (unrealL _) _ _)
        map_smul' := fun c x => Subtype.ext (map_smul (unrealL _) _ _)
        left_inv := fun x => Subtype.ext ((unrealL _).symm_apply_apply _)
        right_inv := fun Y => Subtype.ext ((unrealL _).apply_symm_apply _) }
    have h := @haar_of_equiv (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra _ _ _ _ _ _ _ _
      (inferInstance : MeasurableSpace (Mt k r))
      (inferInstance : BorelSpace (Mt k r)) _ _ isFilB isAdjB volume _ e
    rw [← Nset_eq] at h
    rw [haarLie, one_smul]
    exact h
  · obtain ⟨C, M, hC, h⟩ := growth_of_equiv (isFilB (k := k) (r := r)) (unrealL (2 * r + k + 1))
    refine ⟨C, M, hC, fun Y hY => ?_⟩
    rw [lieOf_Nset_eq] at hY
    rw [sqrt_hs, sqrt_hs]
    exact h Y (mem_lieN.mp hY).1

theorem b4 : NsetExpInjectiveSurjective := unipotent_exp_haar_sqrt_bound

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
