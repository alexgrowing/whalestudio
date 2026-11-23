import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.MatSmooth

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem mul_bd (x y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (x * y)‖ ≤ a * (‖toL x‖ * ‖toL y‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖∑ k, x i k * y k j‖ ≤ _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL x‖ * ‖toL y‖) fun k _ => ?_).trans (by simp))
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
  · exact (norm_le_pi_norm (toL x i) k).trans (norm_le_pi_norm (toL x) i)
  · exact (norm_le_pi_norm (toL y k) j).trans (norm_le_pi_norm (toL y) k)

private theorem star_bd (x : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (star x)‖ ≤ ‖toL x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖star (x j i)‖ ≤ _
  rw [norm_star]
  exact (norm_le_pi_norm (toL x j) i).trans (norm_le_pi_norm (toL x) j)

private theorem sand_bd {C : ℝ} (h : GL (Fin a) (Cinf E)) (hC : ‖toL h.val‖ ≤ C) (v : HV E a) :
    ‖sand h v‖ ≤ (a * a * C * C) * ‖v‖ := by
  have h0 : 0 ≤ C := (norm_nonneg _).trans hC
  change ‖toL (h.val * Matrix.of v.1 * star h.val)‖ ≤ _
  have h1 : ‖toL (h.val * Matrix.of v.1)‖ ≤ a * (C * ‖v‖) :=
    (mul_bd _ _).trans (by
      change (a : ℝ) * (‖toL h.val‖ * ‖v‖) ≤ _
      gcongr)
  calc _ ≤ _ := mul_bd _ _
    _ ≤ a * ((a * (C * ‖v‖)) * C) := by
      gcongr
      exact (star_bd _).trans hC
    _ = _ := by ring

private theorem exists_cpt (C : ℝ) : ∃ K : Set (Lie E a), IsCompact K ∧ K ⊆ invSet E a ∧
    ∀ h : GL (Fin a) (Cinf E), ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C → toL h.val ∈ K := by
  have hc : IsClosed {z : Lie E a × Lie E a | toL (Matrix.of z.1 * Matrix.of z.2) = toL 1} := by
    refine isClosed_eq ?_ continuous_const
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun z : Lie E a × Lie E a => ∑ k, z.1 i k * z.2 k j
    fun_prop
  refine ⟨Prod.fst '' ((Metric.closedBall 0 C ×ˢ Metric.closedBall 0 C) ∩ _),
    (((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right hc).image continuous_fst, ?_, ?_⟩
  · rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
    have e : Matrix.of z.1 * Matrix.of z.2 = 1 := hz
    exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse e)
  · intro h h1 h2
    exact ⟨(toL h.val, toL (h⁻¹).val), ⟨⟨mem_closedBall_zero_iff.2 h1, mem_closedBall_zero_iff.2 h2⟩,
      congrArg toL h.mul_inv⟩, rfl⟩

private theorem mat_bd (Ξ : AlgRep E a) (C : ℝ) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ h : GL (Fin a) (Cinf E), ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C → ∀ y, ‖Ξ.mat h *ᵥ y‖ ≤ B * ‖y‖ := by
  obtain ⟨K, hK, hs, hm⟩ := exists_cpt (E := E) (a := a) C
  have hb : ∀ i j, ∃ b : ℝ, ∀ x ∈ K, ‖extGL (fun y => Ξ.mat y i j) x‖ ≤ b := fun i j =>
    hK.exists_bound_of_continuousOn ((matSmooth E a Ξ i j).1.continuousOn.mono hs)
  choose b hb using hb
  have h0 : 0 ≤ ∑ i, ∑ j, |b i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ i, ∑ j, |b i j|, h0, fun h h1 h2 y => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_⟩
  change ‖∑ j, Ξ.mat h i j * y j‖ ≤ _
  calc _ ≤ ∑ j, |b i j| * ‖y‖ := by
        refine norm_sum_le_of_le _ fun j _ => (norm_mul_le _ _).trans
          (mul_le_mul ?_ (norm_le_pi_norm y j) (norm_nonneg _) (abs_nonneg _))
        have := hb i j _ (hm h h1 h2)
        rw [extGL_val] at this
        exact this.trans (le_abs_self _)
    _ = (∑ j, |b i j|) * ‖y‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, |b i j|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)) (norm_nonneg _)

end

theorem UpperTheory.V.Lit.Geo.matBd :
    MatBd := by
  intro E _ _ _ a Ξ C
  obtain ⟨B, hB, h⟩ := mat_bd Ξ C
  refine ⟨max B (a * a * C * C), le_max_of_le_left hB, fun g h1 h2 => ⟨fun y => (h g h1 h2 y).trans ?_,
    fun v => (sand_bd g h1 v).trans ?_, fun v => (sand_bd g⁻¹ h2 v).trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
