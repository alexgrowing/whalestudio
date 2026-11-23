import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace LieAlgebraAction

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def lmL (A : LieI ι a) : LieI ι a →ₗ[ℝ] LieI ι a where
  toFun Z := Matrix.of.symm (Matrix.of A * Matrix.of Z)
  map_add' x y := by
    change Matrix.of.symm (Matrix.of A * (Matrix.of x + Matrix.of y)) = _
    rw [Matrix.mul_add]; rfl
  map_smul' c x := by
    change Matrix.of.symm (Matrix.of A * (c • Matrix.of x)) = _
    rw [Matrix.mul_smul]; rfl

def lmC : LieI ι a →ₗ[ℝ] (LieI ι a →L[ℝ] LieI ι a) where
  toFun A := LinearMap.toContinuousLinearMap (lmL A)
  map_add' A B := by
    ext1 Z
    change Matrix.of.symm ((Matrix.of A + Matrix.of B) * Matrix.of Z) = _
    rw [Matrix.add_mul]; rfl
  map_smul' c A := by
    ext1 Z
    change Matrix.of.symm ((c • Matrix.of A) * Matrix.of Z) = _
    rw [Matrix.smul_mul]; rfl

def lm : LieI ι a →L[ℝ] (LieI ι a →L[ℝ] LieI ι a) := LinearMap.toContinuousLinearMap lmC

theorem isOpen_U : IsOpen {M : LieI ι a | IsUnit (Matrix.of M)} := by
  have : {M : LieI ι a | IsUnit (Matrix.of M)} = (fun M : LieI ι a => (Matrix.of M).det) ⁻¹' {u | IsUnit u} := by
    ext M; exact Matrix.isUnit_iff_isUnit_det _
  rw [this]
  refine Units.isOpen.preimage (Continuous.matrix_det ?_)
  exact continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i)

def invL (M : LieI ι a) : LieI ι a := Matrix.of.symm (Matrix.of M)⁻¹

theorem lm_inv_mul {M : LieI ι a} (hM : IsUnit (Matrix.of M)) (Z : LieI ι a) : lm (invL M) (lm M Z) = Z := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hM
  change Matrix.of.symm ((Matrix.of M)⁻¹ * (Matrix.of M * Matrix.of Z)) = Z
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd]; rfl

theorem lm_mul_inv {M : LieI ι a} (hM : IsUnit (Matrix.of M)) (Z : LieI ι a) : lm M (lm (invL M) Z) = Z := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hM
  change Matrix.of.symm (Matrix.of M * ((Matrix.of M)⁻¹ * Matrix.of Z)) = Z
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hd]; rfl

theorem isUnit_lm {M : LieI ι a} (hM : IsUnit (Matrix.of M)) : IsUnit (lm M) :=
  ⟨⟨lm M, lm (invL M), ContinuousLinearMap.ext fun Z => lm_mul_inv hM Z,
    ContinuousLinearMap.ext fun Z => lm_inv_mul hM Z⟩, rfl⟩

theorem inverse_lm {M : LieI ι a} (hM : IsUnit (Matrix.of M)) : Ring.inverse (lm M) = lm (invL M) := by
  have : (⟨lm M, lm (invL M), ContinuousLinearMap.ext fun Z => lm_mul_inv hM Z,
    ContinuousLinearMap.ext fun Z => lm_inv_mul hM Z⟩ : (LieI ι a →L[ℝ] LieI ι a)ˣ) = (isUnit_lm hM).unit :=
    Units.ext rfl
  have h2 := Ring.inverse_unit (isUnit_lm hM).unit
  rw [← this] at h2
  exact h2

omit [Fintype ι] in
theorem orb_unit (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) {M : LieI ι a} (hM : IsUnit (Matrix.of M)) :
    orb ρ v M = ρ hM.unit v := by
  unfold orb; rw [dif_pos hM]

omit [Fintype ι] in
theorem orb_mul (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) (g : GL (Fin a) (ι → ℂ)) (M : LieI ι a) :
    orb ρ v (Matrix.of.symm (g.val * Matrix.of M)) = ρ g (orb ρ v M) := by
  by_cases hM : IsUnit (Matrix.of M)
  · have h' : IsUnit (Matrix.of (Matrix.of.symm (g.val * Matrix.of M))) := by
      change IsUnit (g.val * Matrix.of M); exact g.isUnit.mul hM
    rw [orb_unit ρ v h', orb_unit ρ v hM]
    have : h'.unit = g * hM.unit := Units.ext rfl
    rw [this, map_mul]; rfl
  · have h' : ¬ IsUnit (Matrix.of (Matrix.of.symm (g.val * Matrix.of M))) := by
      intro h
      apply hM
      have e : Matrix.of M = (g⁻¹).val * (g.val * Matrix.of M) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      rw [e]; exact (g⁻¹).isUnit.mul h
    unfold orb; rw [dif_neg hM, dif_neg h', map_zero]

theorem hasFDerivAt_orb (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) {v : X} {D : LieI ι a →L[ℝ] X}
    (hD : HasFDerivAt (orb ρ v) D (oneI ι a)) {M : LieI ι a} (hM : IsUnit (Matrix.of M)) :
    HasFDerivAt (orb ρ v) ((((ρ hM.unit).restrictScalars ℝ).comp D).comp (Ring.inverse (lm M))) M := by
  rw [inverse_lm hM]
  have h1 : lm (invL M) M = oneI ι a := by
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp hM
    change Matrix.of.symm ((Matrix.of M)⁻¹ * Matrix.of M) = Matrix.of.symm 1
    rw [Matrix.nonsing_inv_mul _ hd]
  have hD' : HasFDerivAt (orb ρ v) D (lm (invL M) M) := by rw [h1]; exact hD
  have hc := (((ρ hM.unit).restrictScalars ℝ).hasFDerivAt).comp M (hD'.comp M (lm (invL M)).hasFDerivAt)
  refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun Z => ?_)
  change orb ρ v Z = ρ hM.unit (orb ρ v (lm (invL M) Z))
  rw [← orb_mul]
  congr 1
  exact (lm_mul_inv hM Z).symm

theorem fderiv_orb (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) {v : X} {D : LieI ι a →L[ℝ] X}
    (hD : HasFDerivAt (orb ρ v) D (oneI ι a)) {M : LieI ι a} (hM : IsUnit (Matrix.of M))
    {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ (LieI ι a)) :
    fderiv ℝ (orb ρ v) M = ∑ i, ((LinearMap.toContinuousLinearMap (b.coord i)).comp
      (Ring.inverse (lm M))).smulRight (orb ρ (D (b i)) M) := by
  rw [(hasFDerivAt_orb ρ hD hM).fderiv]
  ext1 Z
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← b.sum_repr (Ring.inverse (lm M) Z)]
  rw [map_sum, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, orb_unit ρ _ hM]
  rfl

end LieAlgebraAction

open LieAlgebraAction in
theorem lie_algebra_action_exists : S1 := by
  intro ι _ a X _ _ _ ρ _ 𝒮 hS
  choose D hD hDS using hS
  let b := Module.finBasis ℝ (LieI ι a)
  have key : ∀ N : ℕ, ∀ v (hv : v ∈ 𝒮), ContDiffOn ℝ N (orb ρ v) {M | IsUnit (Matrix.of M)} := by
    intro N
    induction N with
    | zero =>
      intro v hv
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun M hM => (hasFDerivAt_orb ρ (hD v hv) hM).continuousAt.continuousWithinAt
    | succ N ih =>
      intro v hv
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_U]
      refine ⟨fun M hM => (hasFDerivAt_orb ρ (hD v hv) hM).differentiableAt.differentiableWithinAt,
        fun h => by simp at h, ?_⟩
      have hR : ContDiffOn ℝ N (fun M : LieI ι a => Ring.inverse (lm M)) {M | IsUnit (Matrix.of M)} := by
        intro M hM
        obtain ⟨u, hu⟩ := isUnit_lm hM
        have h1 : ContDiffAt ℝ N Ring.inverse (u : LieI ι a →L[ℝ] LieI ι a) := contDiffAt_ringInverse (𝕜 := ℝ) u
        rw [hu] at h1
        exact (h1.comp M ((lm (ι := ι) (a := a)).contDiff.contDiffAt)).contDiffWithinAt
      have hsum : ContDiffOn ℝ N (fun M : LieI ι a => ∑ i, ((LinearMap.toContinuousLinearMap (b.coord i)).comp
          (Ring.inverse (lm M))).smulRight (orb ρ (D v hv (b i)) M)) {M | IsUnit (Matrix.of M)} :=
        ContDiffOn.sum fun i _ =>
          ((contDiffOn_const (c := LinearMap.toContinuousLinearMap (b.coord i))).clm_comp hR).smulRight
            (ih _ (hDS v hv (b i)))
      exact hsum.congr fun M hM => fderiv_orb ρ (hD v hv) hM b
  intro v hv
  exact contDiffOn_infty.mpr fun N => key N v hv

end PositivityTheory.jumpWindows

end
