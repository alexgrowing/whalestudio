import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem col_eq {k : Type} [Field k] (g r : GL (Fin 2) k) (a b : k) (h10 : (g * r * g⁻¹ : GL (Fin 2) k) 1 0 = 0)
    (h00 : (g * r * g⁻¹ : GL (Fin 2) k) 0 0 = a) (h11 : (g * r * g⁻¹ : GL (Fin 2) k) 1 1 = b) :
    r 0 0 * g⁻¹ 0 0 + r 0 1 * g⁻¹ 1 0 = a * g⁻¹ 0 0 ∧ r 1 0 * g⁻¹ 0 0 + r 1 1 * g⁻¹ 1 0 = a * g⁻¹ 1 0 ∧
      r 0 0 + r 1 1 = a + b := by
  have e : ((r : Matrix (Fin 2) (Fin 2) k) * (g⁻¹ : GL (Fin 2) k)) =
      ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g * r * g⁻¹ : GL (Fin 2) k) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 1) 0
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at e0 e1
  have t : Matrix.trace ((g * r * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      Matrix.trace (r : Matrix (Fin 2) (Fin 2) k) := by
    rw [Units.val_mul, Matrix.trace_mul_comm, ← Units.val_mul, inv_mul_cancel_left]
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two] at t
  rw [h10, h00] at e0 e1
  rw [h00, h11] at t
  refine ⟨?_, ?_, t.symm⟩
  · rw [e0]; ring
  · rw [e1]; ring

theorem UpperTheory.symmetric_cube_line_exists :
    UpperTheory.V.Sd.S3.LineEx := by
  intro l _ Γ _ H ρ ξ κ hρ ⟨g, hg⟩ hκ ⟨s₀, hs₀, hne⟩
  have key := fun s : H => col_eq g (ρ s) _ _ ((hg s).1 1 0 (by decide)) ((hg s).2 0) ((hg s).2 1)
  have hdet : (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 -
      (g⁻¹ : GL (Fin 2) (Qbar l)) 0 1 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 ≠ 0 := by
    have := (g⁻¹).det_ne_zero
    rwa [Matrix.det_fin_two] at this
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 = p at key hdet
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 = q at key hdet
  have hge : 1 ≤ ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1‖ := by
    by_contra hlt
    apply hne
    have h1 : ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - (ξ s₀ : Qbar l)‖ < 1 := hκ ⟨s₀, hs₀⟩
    rw [norm_sub_rev] at h1
    have e : (ξ s₀ : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) = ((ξ s₀ : Qbar l) - (κ 0 ⟨s₀, hs₀⟩ : Qbar l)) +
        (((κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1) + (ρ s₀ 1 1 - 1)) := by
      rw [Units.val_one]; ring
    unfold Cong
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 ?_)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (not_le.mp hlt) (hρ s₀).1)
  have hqp : ‖q‖ ≤ ‖p‖ := by
    have e : ((κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1) * q = ρ s₀ 1 0 * p := by
      have := (key ⟨s₀, hs₀⟩).2.1
      simp only at this
      linear_combination -this
    calc ‖q‖ ≤ ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1‖ * ‖q‖ := le_mul_of_one_le_left (norm_nonneg _) hge
      _ = ‖ρ s₀ 1 0‖ * ‖p‖ := by rw [← norm_mul, e, norm_mul]
      _ ≤ ‖p‖ := mul_le_of_le_one_left (norm_nonneg _) (hρ s₀).2
  have hp : p ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_le_zero_iff] at hqp
    simp [hqp] at hdet
  refine ⟨q / p, ?_, fun s => ?_⟩
  · rw [norm_div]
    exact div_le_one_of_le₀ hqp (norm_nonneg _)
  · obtain ⟨k1, k2, k3⟩ := key s
    have a1 : ρ s 0 0 + ρ s 0 1 * (q / p) = κ 0 s := by
      field_simp
      linear_combination k1
    refine ⟨a1, ?_, ?_⟩
    · field_simp
      linear_combination k2
    · linear_combination k3 - a1
