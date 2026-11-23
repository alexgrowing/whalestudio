import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af Filter Topology
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def jor (X Y : HV E a) : HV E a :=
  ⟨toL (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1), by
    have hX : star (Matrix.of X.1) = Matrix.of X.1 := X.2
    have hY : star (Matrix.of Y.1) = Matrix.of Y.1 := Y.2
    change star (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1) =
      Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1
    rw [star_add, star_mul, star_mul, hX, hY, add_comm]⟩

private def jorL : HV E a →ₗ[ℝ] HV E a →ₗ[ℝ] HV E a :=
  LinearMap.mk₂ ℝ jor
    (fun X X' Y => Subtype.ext (by
      change (Matrix.of X.1 + Matrix.of X'.1) * Matrix.of Y.1 + Matrix.of Y.1 * (Matrix.of X.1 + Matrix.of X'.1) =
        (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1) +
          (Matrix.of X'.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X'.1)
      rw [add_mul, mul_add]; abel))
    (fun c X Y => Subtype.ext (by
      change (c • Matrix.of X.1) * Matrix.of Y.1 + Matrix.of Y.1 * (c • Matrix.of X.1) =
        c • (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1)
      rw [smul_mul_assoc, mul_smul_comm, smul_add]))
    (fun X Y Y' => Subtype.ext (by
      change Matrix.of X.1 * (Matrix.of Y.1 + Matrix.of Y'.1) + (Matrix.of Y.1 + Matrix.of Y'.1) * Matrix.of X.1 =
        (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1) +
          (Matrix.of X.1 * Matrix.of Y'.1 + Matrix.of Y'.1 * Matrix.of X.1)
      rw [add_mul, mul_add]; abel))
    (fun c X Y => Subtype.ext (by
      change Matrix.of X.1 * (c • Matrix.of Y.1) + (c • Matrix.of Y.1) * Matrix.of X.1 =
        c • (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1)
      rw [smul_mul_assoc, mul_smul_comm, smul_add]))

private def jorC : HV E a →L[ℝ] HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := HV E a) (F' := HV E a)).toLinearMap ∘ₗ jorL)

private theorem jorC_val (X Y : HV E a) :
    Matrix.of (jorC X Y).1 = Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1 := rfl

private def sq2 (X : HV E a) : HV E a := (1 / 2 : ℝ) • jorC X X

private theorem square_map_val (X : HV E a) : Matrix.of (sq2 X).1 = Matrix.of X.1 * Matrix.of X.1 := by
  change (1 / 2 : ℝ) • Matrix.of (jorC X X).1 = _
  rw [jorC_val, ← two_smul ℝ, smul_smul]; norm_num

private theorem square_map_one : sq2 (hOne E a) = hOne E a := by
  apply Subtype.ext
  change Matrix.of (sq2 (hOne E a)).1 = Matrix.of (hOne E a).1
  rw [square_map_val, hOne_val, mul_one]

private theorem square_map_contDiff : ContDiff ℝ ∞ (sq2 (E := E) (a := a)) :=
  ((jorC (E := E) (a := a)).contDiff.clm_apply contDiff_id).const_smul _

private def dbl : HV E a ≃L[ℝ] HV E a :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := HV E a) (Units.mk0 (2 : ℝ) two_ne_zero)

private theorem square_map_hasFDerivAt : HasFDerivAt (sq2 (E := E) (a := a)) (dbl (E := E) (a := a) : HV E a →L[ℝ] HV E a) (hOne E a) := by
  have h := (((jorC (E := E) (a := a)).hasFDerivAt (x := hOne E a)).clm_apply (hasFDerivAt_id (hOne E a))).const_smul (1 / 2 : ℝ)
  refine HasFDerivAt.congr_fderiv h ?_
  refine ContinuousLinearMap.ext fun H => Subtype.ext ?_
  change (1 / 2 : ℝ) • (Matrix.of (jorC (hOne E a) H).1 + Matrix.of (jorC H (hOne E a)).1) = (2 : ℝ) • Matrix.of H.1
  rw [jorC_val, jorC_val, hOne_val, mul_one, one_mul]
  module

private theorem exists_sqrt : ∃ σ : HV E a → HV E a, ContDiffAt ℝ ∞ σ (hOne E a) ∧ σ (hOne E a) = hOne E a ∧
    ∀ᶠ p in 𝓝 (hOne E a), sq2 (σ p) = p := by
  have hc : ContDiffAt ℝ ∞ (sq2 (E := E) (a := a)) (hOne E a) := square_map_contDiff.contDiffAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hc.localInverse square_map_hasFDerivAt hn, ?_, ?_, ?_⟩
  · have := hc.to_localInverse square_map_hasFDerivAt hn
    rwa [square_map_one] at this
  · have := hc.localInverse_apply_image square_map_hasFDerivAt hn
    rwa [square_map_one] at this
  · have := (hc.hasStrictFDerivAt' square_map_hasFDerivAt hn).eventually_right_inverse
    rwa [square_map_one] at this

private theorem ev_unit : ∀ᶠ X in 𝓝 (hOne E a), IsUnit (Matrix.of X.1) := by
  have hc : Continuous fun X : HV E a => (Matrix.of X.1).det :=
    Continuous.matrix_det (A := fun X : HV E a => Matrix.of X.1) continuous_subtype_val
  have h1 : (Matrix.of (hOne E a).1).det ∈ {x : Cinf E | IsUnit x} := by
    rw [hOne_val, det_one]; exact isUnit_one
  filter_upwards [hc.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds h1)] with X hX
  exact (Matrix.isUnit_iff_isUnit_det _).2 hX

private def lmul (g : Matrix (Fin a) (Fin a) (Cinf E)) : HV E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (g * Matrix.of X.1)
      map_add' := fun X Y => by
        change g * (Matrix.of X.1 + Matrix.of Y.1) = g * Matrix.of X.1 + g * Matrix.of Y.1
        rw [mul_add]
      map_smul' := fun c X => by
        change g * (c • Matrix.of X.1) = c • (g * Matrix.of X.1)
        rw [mul_smul_comm] }

open Classical in
theorem locSec : LocSec := by
  rintro E _ _ a p₀ ⟨g, rfl⟩
  obtain ⟨σ, hσ, hσ1, hσ2⟩ := exists_sqrt (E := E) (a := a)
  have h0 : sand g⁻¹ (sand g (hOne E a)) = hOne E a := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have hq : Tendsto (sand g⁻¹) (𝓝 (sand g (hOne E a))) (𝓝 (hOne E a)) := by
    have := (sand g⁻¹).continuous.tendsto (sand g (hOne E a))
    rwa [h0] at this
  have hs : Tendsto σ (𝓝 (hOne E a)) (𝓝 (hOne E a)) := by
    have := hσ.continuousAt.tendsto
    rwa [hσ1] at this
  have hu := (hs.comp hq).eventually ev_unit
  let u : HV E a → GL (Fin a) (Cinf E) := fun X => if h : IsUnit (Matrix.of X.1) then h.unit else 1
  have hval : ∀ X : HV E a, IsUnit (Matrix.of X.1) → (u X).val = Matrix.of X.1 := fun X h => by
    simp only [u, dif_pos h, IsUnit.unit_spec]
  refine ⟨fun p => g * u (σ (sand g⁻¹ p)), ?_, ?_⟩
  · have h1 : ContDiffAt ℝ ∞ (fun p => σ (sand g⁻¹ p)) (sand g (hOne E a)) :=
      ContDiffAt.comp (g := σ) _ (h0.symm ▸ hσ) (sand g⁻¹).contDiff.contDiffAt
    refine ((lmul g.val).contDiff.contDiffAt.comp _ h1).congr_of_eventuallyEq ?_
    filter_upwards [hu] with p hp
    rw [Units.val_mul, hval (σ (sand g⁻¹ p)) hp]; rfl
  · filter_upwards [hu, hq.eventually hσ2] with p hp hp2
    have h2 : sand (u (σ (sand g⁻¹ p))) (hOne E a) = sand g⁻¹ p := by
      rw [← hp2]
      apply Subtype.ext
      change Matrix.of (sand _ _).1 = Matrix.of (sq2 _).1
      have hX : star (Matrix.of (σ (sand g⁻¹ p)).1) = Matrix.of (σ (sand g⁻¹ p)).1 := (σ (sand g⁻¹ p)).2
      rw [sand_val, square_map_val, hOne_val, mul_one, hp2, hval (σ (sand g⁻¹ p)) hp, hX]
    rw [map_mul, ContinuousLinearMap.mul_apply, h2, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

end UpperTheory.V.Lit.Dr
