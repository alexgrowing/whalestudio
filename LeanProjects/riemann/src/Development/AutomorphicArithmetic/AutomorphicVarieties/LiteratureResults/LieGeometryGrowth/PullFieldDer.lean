import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem lie_bound {φ : Sm E a} (h : BddDer φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (X : Lie E a) (g : GA E a), ‖(lie E a X φ).1 g‖ ≤ B * ‖X‖ := by
  let b := Module.finBasis ℝ (Lie E a)
  choose c hc using fun k => h (b k) []
  have hc' : ∀ k g, ‖(lie E a (b k) φ).1 g‖ ≤ c k := fun k g => by simpa using hc k g
  have h0 : ∀ k, 0 ≤ c k := fun k => (norm_nonneg _).trans (hc' k 1)
  refine ⟨∑ k, ‖LinearMap.toContinuousLinearMap (b.coord k)‖ * c k,
    Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (h0 k), fun X g => ?_⟩
  let L : Lie E a →ₗ[ℝ] ℂ :=
    { toFun := fun X => (lie E a X φ).1 g
      map_add' := fun X X' => by rw [map_add]; rfl
      map_smul' := fun r X => by rw [map_smul]; rfl }
  have e : L X = ∑ k, b.repr X k • L (b k) := by
    conv_lhs => rw [← b.sum_repr X]
    simp only [map_sum, map_smul]
  change ‖L X‖ ≤ _
  rw [e, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul, mul_right_comm]
  exact mul_le_mul ((LinearMap.toContinuousLinearMap (b.coord k)).le_opNorm X) (hc' k g) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem val_bound {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a} {C : ℝ} (h : IsFld U Y C)
    (g : GA E a) : ‖hv (Y g)‖ ≤ a * C ^ 2 + 1 := by
  obtain ⟨x, h1, h2, -⟩ := h.root g 1 (by simp)
  have hC : 0 ≤ C := (norm_nonneg _).trans h2
  have hp : (0 : ℝ) ≤ a * C ^ 2 + 1 := by positivity
  have e : (Y g).1 = x.val * star x.val - 1 := by rw [h1, one_smul, add_sub_cancel_left]
  have hx : ∀ i j, ‖x.val i j‖ ≤ C := fun i j =>
    ((norm_le_pi_norm (toL x.val i) j).trans (norm_le_pi_norm (toL x.val) i)).trans h2
  change ‖toL (Y g).1‖ ≤ _
  refine (pi_norm_le_iff_of_nonneg hp).2 fun i => (pi_norm_le_iff_of_nonneg hp).2 fun j => ?_
  change ‖(Y g).1 i j‖ ≤ _
  rw [e, Matrix.sub_apply, Matrix.mul_apply]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sum_le _ _).trans ?_) ?_)
  · calc ∑ k, ‖x.val i k * star x.val k j‖ ≤ ∑ _k : Fin a, C ^ 2 := Finset.sum_le_sum fun k _ => by
          refine (norm_mul_le _ _).trans ?_
          rw [Matrix.star_apply, norm_star, sq]
          exact mul_le_mul (hx i k) (hx j k) (norm_nonneg _) hC
      _ = a * C ^ 2 := by simp
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp

theorem fieldDer : FieldDer := by
  intro E _ _ _ a U Y C h
  choose φ hφ hb using h.sm
  choose B hB0 hB using fun i j w => lie_bound (hb i j w)
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (HV E a).subtype (Submodule.ker_subtype _)
  have hP' : ∀ v : HV E a, LinearMap.toContinuousLinearMap P v.1 = v := fun v => LinearMap.congr_fun hP v
  let B' : Lie E a := fun i j w => (B i j w : ℂ)
  have hle : ∀ i j w, B i j w ≤ ‖B'‖ := fun i j w =>
    calc B i j w ≤ ‖B' i j w‖ := by simpa [B'] using le_abs_self _
      _ ≤ ‖B'‖ := ((norm_le_pi_norm (B' i j) w).trans (norm_le_pi_norm (B' i) j)).trans (norm_le_pi_norm B' i)
  refine ⟨max (a * C ^ 2 + 1) (‖LinearMap.toContinuousLinearMap P‖ * ‖B'‖), le_max_of_le_left (by positivity),
    fun g => ⟨le_max_of_le_left (val_bound h g), fun c X h0 hX => ?_⟩⟩
  let D : Lie E a := fun i j w => (lie E a X (φ i j w)).1 g
  have hD : HasDerivAt (fun t => (hv (Y (g * infGL E a (c t)))).1) D 0 :=
    hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w =>
      (hasDerivAt_curve (φ i j w) g c X h0 hX).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => (hφ i j w _).symm)
  have hn : ‖D‖ ≤ ‖B'‖ * ‖X‖ := by
    have hp : 0 ≤ ‖B'‖ * ‖X‖ := by positivity
    exact (pi_norm_le_iff_of_nonneg hp).2 fun i => (pi_norm_le_iff_of_nonneg hp).2 fun j =>
      (pi_norm_le_iff_of_nonneg hp).2 fun w =>
        (hB i j w X g).trans (mul_le_mul_of_nonneg_right (hle i j w) (norm_nonneg _))
  refine ⟨LinearMap.toContinuousLinearMap P D, ?_, ?_⟩
  · refine ((LinearMap.toContinuousLinearMap P).le_opNorm_of_le hn).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · exact ((LinearMap.toContinuousLinearMap P).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => (hP' _).symm)

end UpperTheory.V.Lit.Geo
