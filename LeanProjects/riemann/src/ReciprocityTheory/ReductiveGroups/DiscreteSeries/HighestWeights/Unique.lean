import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.UniqueA

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma uq_offdiag_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X)
    {a b : Fin n} (hab : ε a ≠ ε b) : X a b = 0 := by
  have hd : (if ε a then (1 : ℂ) else -1) ≠ (if ε b then (1 : ℂ) else -1) := by
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab ⊢ <;> norm_num
  have h := congrFun (congrFun hX a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h2 : X a b * ((if ε b then (1 : ℂ) else -1) - (if ε a then (1 : ℂ) else -1)) = 0 := by
    rw [mul_sub, h]; ring
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3).symm hd

lemma uq_kHighest {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.KHighest ε (kunits T) Λ T.w :=
  ⟨fun a => T.w_wt a, fun a b hab he => T.w_hw a b hab he⟩

theorem kType_unique {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T T' : KType ε Λ) :
    ∃ φ : T.V ≃ₗᵢ[ℂ] T'.V, (∀ (k : KG ε) (v : T.V), φ (T.op k v) = T'.op k (φ v)) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, X * Jm ε = Jm ε * X → ∀ v : T.V, φ (T.dτ X v) = T'.dτ X (φ v)) ∧
      φ T.w = T'.w := by
  obtain ⟨φ, hφF, hφw⟩ := uq_exists_isometry ε (kunits T) (kunits T') Λ T.w T'.w (KType.kRel T)
    (KType.kRel T') (KType.kUnit T) (KType.kUnit T') (uq_kHighest T) (uq_kHighest T') T.w_norm
    T'.w_norm (KType.kSpan_eq_top T) (KType.kSpan_eq_top T')
  have expand : ∀ (S : KType ε Λ) (X : Matrix (Fin n) (Fin n) ℂ) (u : S.V),
      S.dτ X u = ∑ a, ∑ b, X a b • S.dτ (Matrix.single a b 1) u := by
    intro S X u
    have hs : ∀ i j, Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := fun i j => by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [hs, map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  have hdτ : ∀ X : Matrix (Fin n) (Fin n) ℂ, X * Jm ε = Jm ε * X → ∀ v : T.V,
      φ (T.dτ X v) = T'.dτ X (φ v) := by
    intro X hX v
    rw [expand T X v, expand T' X (φ v), map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases h : ε a = ε b
    · rw [map_smul]
      congr 1
      exact hφF a b h v
    · rw [uq_offdiag_zero hX h, zero_smul, zero_smul, map_zero]
  refine ⟨φ, ?_, hdτ, hφw⟩
  intro k v
  obtain ⟨Y, hY, hkY⟩ := exists_log ε k
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have h1 : toMK (γ 1) = toMK k := by
    rw [hγ 1, hkY]
    simp
  have hk : γ 1 = k := Subtype.ext (Subtype.ext (Units.ext h1))
  have hop : ∀ S : KType ε Λ, S.op k = NormedSpace.exp (S.dτ Y) := by
    intro S
    rw [← hk, KType.op_curve S hY γ hγ 1]
    simp
  rw [hop T, hop T']
  let f := φ.toContinuousLinearEquiv.conjContinuousAlgEquiv
  have hf : f (T.dτ Y) = T'.dτ Y := by
    ext u
    simp only [f, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, hdτ Y hY.2]
    simp
  letI : NormedAlgebra ℚ (T.V →L[ℂ] T.V) := NormedAlgebra.restrictScalars ℚ ℂ _
  letI : NormedAlgebra ℚ (T'.V →L[ℂ] T'.V) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hexp := NormedSpace.map_exp f (map_continuous f) (T.dτ Y)
  rw [hf] at hexp
  rw [← hexp]
  simp [f, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]

end ReciprocityTheory.ChartRestriction.DS.HW
