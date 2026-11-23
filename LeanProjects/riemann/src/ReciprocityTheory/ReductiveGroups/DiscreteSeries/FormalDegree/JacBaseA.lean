import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarAct
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdShcSqEqJacPow

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

namespace JacB

section Gen

variable {E 𝔸 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
  [CompleteSpace 𝔸]

theorem contDiff_exp_alg : ContDiff ℝ 1 (NormedSpace.exp : 𝔸 → 𝔸) := by
  first
  | exact contDiff_exp
  | exact NormedSpace.contDiff_exp
  | exact (NormedSpace.analyticOnNhd_exp (𝕂 := ℝ)).contDiff
  | exact (analyticOnNhd_exp (𝕂 := ℝ)).contDiff
  | exact contDiff_iff_contDiffAt.mpr fun x =>
      (analyticAt_exp_of_mem_ball (𝕂 := ℝ) x (by simp [expSeries_radius_eq_top])).contDiffAt
  | exact contDiff_iff_contDiffAt.mpr fun x =>
      (NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) x (by simp [NormedSpace.expSeries_radius_eq_top])).contDiffAt

theorem hasFDerivAt_exp_alg (x : 𝔸) :
    HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸) (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) x) x := by
  first
  | exact ((contDiff_exp_alg (𝔸 := 𝔸)).differentiable one_ne_zero x).hasFDerivAt
  | exact ((contDiff_exp_alg (𝔸 := 𝔸)).differentiable le_rfl x).hasFDerivAt

theorem fderiv_exp_eq {x W D : 𝔸} (h : HasDerivAt (fun s : ℝ => NormedSpace.exp (x + s • W)) D 0) :
    fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) x W = D := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • W) W 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const W).const_add x
  have h2 := (hasFDerivAt_exp_alg (x + (0 : ℝ) • W)).comp_hasDerivAt (0 : ℝ) h1
  rw [zero_smul, add_zero] at h2
  exact h2.unique h

theorem contDiffAt_of_exp [FiniteDimensional ℝ 𝔸] {f : E → 𝔸} {z : E} (hf : ContinuousAt f z)
    (hg : ContDiffAt ℝ 1 (fun w => NormedSpace.exp (f w)) z)
    (hi : Function.Injective (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (f z))) :
    ContDiffAt ℝ 1 f z := by
  let e : 𝔸 ≃L[ℝ] 𝔸 :=
    (LinearEquiv.ofInjectiveEndo
      (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (f z) : 𝔸 →ₗ[ℝ] 𝔸) hi).toContinuousLinearEquiv
  have he : (e : 𝔸 →L[ℝ] 𝔸) = fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (f z) := by
    ext v; rfl
  have hd : HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸) (e : 𝔸 →L[ℝ] 𝔸) (f z) := by
    rw [he]; exact hasFDerivAt_exp_alg _
  have hc : ContDiffAt ℝ 1 (NormedSpace.exp : 𝔸 → 𝔸) (f z) := contDiff_exp_alg.contDiffAt
  have h1 := hc.to_localInverse hd one_ne_zero
  have h2 := (hc.hasStrictFDerivAt' hd one_ne_zero).eventually_left_inverse
  have h3 := ContDiffAt.comp z (g := hc.localInverse hd one_ne_zero) h1 hg
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [hf.eventually h2] with w hw
  exact hw.symm

end Gen

variable {n : ℕ}

theorem shc_pos' (u : ℝ) : 0 < shc u := by
  unfold shc
  split_ifs with h
  · exact one_pos
  · rcases lt_or_gt_of_ne h with hu | hu
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hu) hu
    · exact div_pos (Real.sinh_pos_iff.mpr hu) hu

theorem jac_pos' {ε : Fin n → Bool} (y : PCoord ε → ℂ) : 0 < Jac y := by
  unfold Jac
  exact Finset.prod_pos (fun a _ => Finset.prod_pos (fun b _ => shc_pos' _))

def pmatLin (ε : Fin n → Bool) : (PCoord ε → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := pmat
  map_add' z w := by
    ext a b
    simp only [pmat, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    ext a b
    simp only [pmat, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def crdLin (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun X := fun ab => X ab.1.1 ab.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem crd_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) : crdLin ε (pmat z) = z := by
  funext ab
  show pmat z ab.1.1 ab.1.2 = z ab
  simp only [pmat]
  rw [dif_pos ab.2]

def shcAdLin {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := shcAd y
  map_add' V W := by
    unfold shcAd
    rw [← Matrix.add_mul, ← Matrix.mul_add]
    congr 2
    ext i j
    simp only [Matrix.add_mul, Matrix.add_apply, Matrix.of_apply, mul_add]
  map_smul' c W := by
    unfold shcAd
    rw [RingHom.id_apply, ← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext i j
    simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.of_apply, mul_smul_comm]

theorem shcAd_eq_zero {ε : Fin n → Bool} (y : PCoord ε → ℂ) {W : Matrix (Fin n) (Fin n) ℂ}
    (h : shcAd y W = 0) : W = 0 := by
  unfold shcAd at h
  set U : Matrix (Fin n) (Fin n) ℂ :=
    ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : Uᴴ * U = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.1
  have h2 : U * Uᴴ = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.2
  set S := Matrix.of (fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) with hS
  have h3 : S = 0 := by
    have : Uᴴ * (U * S * Uᴴ) * U = S := by
      calc Uᴴ * (U * S * Uᴴ) * U = (Uᴴ * U) * S * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
        _ = S := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    rw [← this, h, Matrix.mul_zero, Matrix.zero_mul]
  have h4 : Uᴴ * W * U = 0 := by
    ext i j
    have h5 : S i j = 0 := by rw [h3]; rfl
    rw [hS, Matrix.of_apply, mul_eq_zero] at h5
    rcases h5 with h5 | h5
    · exact absurd (Complex.ofReal_eq_zero.1 h5) (shc_pos' _).ne'
    · exact h5
  calc W = (U * Uᴴ) * W * (U * Uᴴ) := by rw [h2, Matrix.one_mul, Matrix.mul_one]
    _ = U * (Uᴴ * W * U) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h4, Matrix.mul_zero, Matrix.zero_mul]

theorem exp_two (X : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp ((2 : ℝ) • X) = NormedSpace.exp X * NormedSpace.exp X := by
  rw [two_smul]
  first
  | exact Matrix.exp_add_of_commute _ _ (Commute.refl X)
  | exact Matrix.exp_add_of_commute (Commute.refl X)
  | exact NormedSpace.exp_add_of_commute (Commute.refl X)

theorem exp_two_actR {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (z : PCoord ε → ℂ) :
    NormedSpace.exp ((2 : ℝ) • pmat (actR g z)) = gᴴ * NormedSpace.exp ((2 : ℝ) • pmat z) * g := by
  obtain ⟨k, hk⟩ := actR_spec hg z
  have hk1 : (toMK k)ᴴ * toMK k = 1 := k.2.1.1
  have hz : (NormedSpace.exp (pmat z))ᴴ = NormedSpace.exp (pmat z) := (pmat_isHermitian z).exp
  have hw : (NormedSpace.exp (pmat (actR g z)))ᴴ = NormedSpace.exp (pmat (actR g z)) :=
    (pmat_isHermitian _).exp
  have h1 : (NormedSpace.exp (pmat z) * g)ᴴ * (NormedSpace.exp (pmat z) * g) =
      (toMK k * NormedSpace.exp (pmat (actR g z)))ᴴ * (toMK k * NormedSpace.exp (pmat (actR g z))) := by
    rw [hk]; rfl
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hz, hw, Matrix.mul_assoc _ (toMK k)ᴴ,
    ← Matrix.mul_assoc (toMK k)ᴴ, hk1, Matrix.one_mul] at h1
  rw [exp_two, exp_two, ← h1]
  simp only [Matrix.mul_assoc]

section Op

open scoped Matrix.Norms.Operator

def pmatC (ε : Fin n → Bool) : (PCoord ε → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (pmatLin ε)

def crdC (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (PCoord ε → ℂ) :=
  LinearMap.toContinuousLinearMap (crdLin ε)

theorem pmat_contDiff (ε : Fin n → Bool) : ContDiff ℝ 1 (fun z : PCoord ε → ℂ => pmat z) := by
  first
  | exact (pmatC ε).contDiff
  | exact ContinuousLinearMap.contDiff (pmatC ε)

theorem actR_continuous {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Continuous (actR (ε := ε) g) := by
  choose k hk using actR_spec hg
  have h1 : Continuous (fun z => (k z, actR g z)) := by
    rw [(polarM_isClosedEmbedding ε).isEmbedding.continuous_iff]
    have h2 : (polarM ∘ fun z => (k z, actR g z)) = fun z => NormedSpace.exp (pmat z) * g := by
      funext z; exact (hk z).symm
    rw [h2]
    exact ((contDiff_exp_alg.comp (pmat_contDiff ε)).mul contDiff_const).continuous
  exact continuous_snd.comp h1

theorem fderiv_exp_two {ε : Fin n → Bool} (y : PCoord ε → ℂ) (W : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • pmat y) W = NormedSpace.exp (pmat y) * shcAd y W * NormedSpace.exp (pmat y) := by
  apply fderiv_exp_eq
  have h := hasDerivAt_exp_two y W
  have e : (fun s : ℝ => NormedSpace.exp ((2 : ℂ) • pmat y + (s : ℂ) • W)) =
      fun s : ℝ => NormedSpace.exp ((2 : ℝ) • pmat y + s • W) := by
    funext s
    rw [two_smul, two_smul, Complex.coe_smul]
  rw [e] at h
  exact h

theorem conj_cancel {A B X : Matrix (Fin n) (Fin n) ℂ}
    (h : NormedSpace.exp X * A * NormedSpace.exp X = NormedSpace.exp X * B * NormedSpace.exp X) :
    A = B := by
  have hu : IsUnit (NormedSpace.exp X) := Matrix.isUnit_exp X
  exact hu.mul_left_cancel (hu.mul_right_cancel h)

theorem fderiv_exp_two_inj {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Function.Injective (fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • pmat y)) := by
  intro W1 W2 hW
  have h0 : fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • pmat y) (W1 - W2) = 0 := by
    rw [map_sub, hW, sub_self]
  rw [fderiv_exp_two] at h0
  have h1 : shcAd y (W1 - W2) = 0 :=
    conj_cancel (X := pmat y) (by rw [h0, Matrix.mul_zero, Matrix.zero_mul])
  exact sub_eq_zero.mp (shcAd_eq_zero y h1)

theorem actR_contDiff' {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ContDiff ℝ 1 (actR (ε := ε) g) := by
  have h1 : ContDiff ℝ 1 (fun z : PCoord ε → ℂ => (2 : ℝ) • pmat (actR g z)) := by
    refine contDiff_iff_contDiffAt.2 fun z => contDiffAt_of_exp ?_ ?_ (fderiv_exp_two_inj _)
    · exact (((pmat_contDiff ε).continuous.comp (actR_continuous hg)).const_smul (2 : ℝ)).continuousAt
    · exact (((contDiff_const (c := gᴴ)).mul
        (contDiff_exp_alg.comp ((pmat_contDiff ε).const_smul (2 : ℝ)))).mul
        (contDiff_const (c := g))).contDiffAt.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w => exp_two_actR hg w)
  have h2 := ((crdC ε).contDiff.comp h1).const_smul (1 / 2 : ℝ)
  convert h2 using 1
  funext z
  change actR g z = (1 / 2 : ℝ) • crdLin ε ((2 : ℝ) • pmat (actR g z))
  rw [map_smul, crd_pmat, smul_smul]
  norm_num

theorem shcAd_fderiv_actR {ε : Fin n → Bool} (y v : PCoord ε → ℂ) :
    shcAd y (pmat (fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 v)) = pmat v := by
  have hg := exp_pmat_inUJ y
  have hY : (NormedSpace.exp (pmat y))ᴴ = NormedSpace.exp (pmat y) := (pmat_isHermitian y).exp
  have hD := ((actR_contDiff' hg).differentiable one_ne_zero 0).hasFDerivAt
  set D := fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0
  have h1 := ((pmatC ε).hasFDerivAt.comp 0 hD).const_smul (2 : ℝ)
  have h2 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
        ((2 : ℝ) • pmat y)) ((2 : ℝ) • pmat (actR (NormedSpace.exp (pmat y)) (0 : PCoord ε → ℂ))) := by
    rw [actR_exp_zero]; exact hasFDerivAt_exp_alg _
  have h3 := HasFDerivAt.comp (0 : PCoord ε → ℂ) h2 h1
  have h4 := ((pmatC ε).hasFDerivAt (x := 0)).const_smul (2 : ℝ)
  have h5 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
        ((2 : ℝ) • pmatC ε (0 : PCoord ε → ℂ)) := by
    rw [map_zero, smul_zero]; exact hasFDerivAt_exp_zero
  have h6 := ((HasFDerivAt.comp (0 : PCoord ε → ℂ) h5 h4).const_mul
    (NormedSpace.exp (pmat y))).mul_const' (NormedSpace.exp (pmat y))
  have h7 := h3.unique (h6.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by
    have := exp_two_actR hg z
    rw [hY] at this
    exact this))
  have h8 := congrArg (fun T => T v) h7
  have h9 : fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • pmat y) ((2 : ℝ) • pmat (D v)) =
      NormedSpace.exp (pmat y) * ((2 : ℝ) • pmat v) * NormedSpace.exp (pmat y) := h8
  rw [fderiv_exp_two] at h9
  have h10 : shcAdLin y ((2 : ℝ) • pmat (D v)) = (2 : ℝ) • pmat v := conj_cancel h9
  rw [map_smul] at h10
  exact smul_right_injective _ (two_ne_zero (α := ℝ)) h10

end Op

theorem jacBase' {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    |LinearMap.det ((fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 :
      (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))| * Jac y = 1 := by
  let S : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ) :=
    LinearMap.toContinuousLinearMap (crdLin ε ∘ₗ shcAdLin y ∘ₗ pmatLin ε)
  have hS : fderiv ℝ (shcAdC y) 0 = S := S.fderiv
  have h1 := detP y
  rw [hS] at h1
  set D := fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 with hD
  have h2 : (S : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) ∘ₗ (D : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) =
      LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    change crdLin ε (shcAd y (pmat (D v))) = v
    rw [hD, shcAd_fderiv_actR, crd_pmat]
  have h3 := congrArg LinearMap.det h2
  rw [LinearMap.det_comp, LinearMap.det_id, h1] at h3
  rw [← abs_of_pos (jac_pos' y), ← abs_mul, mul_comm, h3, abs_one]

end JacB

end ReciprocityTheory.ChartRestriction.DS
