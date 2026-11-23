import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FarLoc

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous mulL mulL_apply)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem cd_det_lemma {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContDiff ℂ ∞ (fun x : Matrix ι ι ℂ => x.det) := by
  have he : ∀ i j : ι, ContDiff ℂ ∞ (fun x : Matrix ι ι ℂ => x i j) := fun i j =>
    contDiff_apply_apply ℂ ℂ i j
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum (fun σ _ => contDiff_const.mul (contDiff_prod (fun i _ => he _ _)))

theorem cd_det : ContDiff ℂ ∞ (fun x : M2 n => x.det) := by
  exact cd_det_lemma

theorem cd_detu1 : ContDiff ℂ ∞ (fun x : M2 n => (u1 x).det) := by
  exact cd_det_lemma.comp contDiff_first_cayley_block

theorem curve_hasDerivAt (X x : M2 n) : HasDerivAt (fun s : ℝ => x * cE X s) (x * X) 0 := by
  have h := (mulL x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (cE_hasDerivAt0 X)
  simp only [Function.comp_def, mulL_apply] at h
  exact h

theorem curve_deriv (Ψ : M2 n → ℂ) (hΨ : ContDiff ℂ ∞ Ψ) (X x : M2 n) :
    HasDerivAt (fun s : ℝ => Ψ (x * cE X s)) (fderiv ℂ Ψ x (x * X)) 0 := by
  have hd : HasFDerivAt Ψ (fderiv ℂ Ψ x) (x * cE X 0) := by
    rw [cE_zero, Matrix.mul_one]
    exact (hΨ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h := (hd.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) (curve_hasDerivAt X x)
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] at h
  exact h

theorem continuous_mR' : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem det_mR_ne' (g : GR n) : (mR g).det ≠ 0 := by
  show ((g : GL (Fin n ⊕ Fin n) ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ).det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin n ⊕ Fin n) ℂ).isUnit).ne_zero

def rD (X x : M2 n) : ℂ := fderiv ℂ (fun x : M2 n => x.det) x (x * X) / x.det

def rA (X x : M2 n) : ℂ := fderiv ℂ (fun x : M2 n => (u1 x).det) x (x * X) / (u1 x).det

private theorem rD_mul_left_eq_of_det_ne_zero (P A X : M2 n) (hP : P.det ≠ 0) : rD X (P * A) = rD X A := by
  unfold rD
  let L : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ P)
  have hL : ∀ y, L y = P * y := fun y => rfl
  have hdet : ∀ B : M2 n, HasFDerivAt (fun x : M2 n => x.det) (fderiv ℂ (fun x : M2 n => x.det) B) B :=
    fun B => ((cd_det (n := n)).differentiable (by simp) B).hasFDerivAt
  have h1 : HasFDerivAt (fun y : M2 n => (P * y).det)
      ((fderiv ℂ (fun x : M2 n => x.det) (P * A)).comp L) A := by
    have := (hdet (P * A)).comp A (L.hasFDerivAt (x := A))
    simp only [Function.comp_def, hL] at this
    exact this
  have h2 : HasFDerivAt (fun y : M2 n => (P * y).det)
      (P.det • fderiv ℂ (fun x : M2 n => x.det) A) A := by
    simp_rw [Matrix.det_mul]
    exact (hdet A).const_mul P.det
  have h4 := congrArg (fun T => T (A * X)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hL] at h4
  rw [Matrix.mul_assoc, h4, Matrix.det_mul, mul_div_mul_left _ _ hP]

theorem rD_up (X : M2 n) (p k : GR n) : rD X (mR p * mR k) = rD X (mR k) := by
  exact rD_mul_left_eq_of_det_ne_zero _ _ X (det_mR_ne' p)

private theorem rA_mul_left_eq_of_u1_mul (D : Matrix (Fin n) (Fin n) ℂ) (P A X : M2 n) (hD : D.det ≠ 0)
    (hu : ∀ y, u1 (P * y) = D * u1 y) : rA X (P * A) = rA X A := by
  unfold rA
  let L : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ P)
  have hL : ∀ y, L y = P * y := fun y => rfl
  have hdet : ∀ B : M2 n, HasFDerivAt (fun x : M2 n => (u1 x).det) (fderiv ℂ (fun x : M2 n => (u1 x).det) B) B :=
    fun B => ((cd_detu1 (n := n)).differentiable (by simp) B).hasFDerivAt
  have h1 : HasFDerivAt (fun y : M2 n => (u1 (P * y)).det)
      ((fderiv ℂ (fun x : M2 n => (u1 x).det) (P * A)).comp L) A := by
    have := (hdet (P * A)).comp A (L.hasFDerivAt (x := A))
    simp only [Function.comp_def, hL] at this
    exact this
  have h2 : HasFDerivAt (fun y : M2 n => (u1 (P * y)).det)
      (D.det • fderiv ℂ (fun x : M2 n => (u1 x).det) A) A := by
    simp_rw [hu, Matrix.det_mul]
    exact (hdet A).const_mul D.det
  have h4 := congrArg (fun T => T (A * X)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hL] at h4
  rw [Matrix.mul_assoc, h4, hu, Matrix.det_mul, mul_div_mul_left _ _ hD]

theorem rA_up (X : M2 n) (p k : GR n) (hp : IsUp p) : rA X (mR p * mR k) = rA X (mR k) := by
  have hD : (toBlocks₂₂ (mR p)).det ≠ 0 := by
    rw [← first_block_of_upper p hp]
    exact det_first_cayley_block_ne_zero p.2
  exact rA_mul_left_eq_of_u1_mul _ _ _ X hD (fun y => first_block_upper_mul p y hp)

theorem continuous_rD (X : M2 n) : Continuous fun k : GR n => rD X (mR k) := by
  unfold rD
  refine Continuous.div ?_ (cd_det.continuous.comp continuous_mR') (fun k => det_mR_ne' k)
  exact ((cd_det.continuous_fderiv (by simp)).comp continuous_mR').clm_apply
    (continuous_mR'.mul continuous_const)

theorem continuous_rA (X : M2 n) : Continuous fun k : GR n => rA X (mR k) := by
  unfold rA
  refine Continuous.div ?_ (cd_detu1.continuous.comp continuous_mR')
    (fun k => (det_u_ne (x := mR k) k.2).1)
  exact ((cd_detu1.continuous_fderiv (by simp)).comp continuous_mR').clm_apply
    (continuous_mR'.mul continuous_const)

end PositivityTheory.Rg.Sw.HSt.FL
