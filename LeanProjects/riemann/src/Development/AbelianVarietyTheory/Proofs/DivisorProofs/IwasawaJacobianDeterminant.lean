import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTriangularConjugateEqDiagonalRatio
open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (emb jacDens)
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.FlagFormDeg (apolar)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.FlagFibre

noncomputable def lowProj {m : ℕ} (b c : Fin m) : (Low m → ℂ) →L[ℂ] ℂ :=
  if h : c < b then ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Low m => ℂ) (⟨(b, c), h⟩ : Low m) else 0

theorem lowProj_apply {m : ℕ} (b c : Fin m) (v : Low m → ℂ) : lowProj b c v = (uni v - 1) b c := by
  by_cases h : c < b
  · simp [lowProj, uni, h, one_apply_ne h.ne']
  · by_cases hbc : b = c
    · subst hbc; simp [lowProj, uni]
    · simp [lowProj, uni, h, hbc, one_apply_ne hbc]

theorem hasFDerivAt_uni_apply {m : ℕ} {u : (Low m → ℂ) → Low m → ℂ} {L : (Low m → ℂ) →L[ℂ] (Low m → ℂ)}
    {x : Low m → ℂ} (hu : HasFDerivAt u L x) (b c : Fin m) :
    HasFDerivAt (fun y => uni (u y) b c) ((lowProj b c).comp L) x := by
  by_cases h : c < b
  · have := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Low m => ℂ) (⟨(b, c), h⟩ : Low m)).hasFDerivAt).comp x hu
    simp only [lowProj, uni, of_apply, dif_pos h]
    exact this
  · simpa [lowProj, uni, h] using (hasFDerivAt_const (𝕜 := ℂ) (if b = c then (1 : ℂ) else 0) x)

theorem mul_low_mul_apply {m : ℕ} (A C : Matrix (Fin m) (Fin m) ℂ) (ξ : Low m → ℂ) (i j : Fin m) :
    (A * (uni ξ - 1) * C) i j = ∑ t : Low m, A i t.1.1 * C t.1.2 j * ξ t := by
  let g : Fin m × Fin m → ℂ := fun u => A i u.1 * C u.2 j * (uni ξ - 1) u.1 u.2
  have hsub : ∑ t : Low m, g t.1 = ∑ u : Fin m × Fin m, g u := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun u : Fin m × Fin m => u.2 < u.1) (by simp) g]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u _ hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hu
    simp only [g, ← lowProj_apply]
    simp [lowProj, not_lt.2 hu]
  have hlow : ∀ t : Low m, g t.1 = A i t.1.1 * C t.1.2 j * ξ t := by
    intro t
    simp only [g, ← lowProj_apply]
    simp [lowProj, t.2]
  rw [← Finset.sum_congr rfl (fun t _ => hlow t), hsub, Fintype.sum_prod_type]
  simp only [g, mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem deriv_flag_eq {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (φ : (Low m → ℂ) → Low m → ℂ)
    (B : (Low m → ℂ) → Matrix (Fin m) (Fin m) ℂ) (x : Low m → ℂ)
    (hB : ∀ᶠ y in 𝓝 x, g * uni y = uni (φ y) * B y) (hφ : DifferentiableAt ℂ φ x)
    (hBd : ∀ a c, DifferentiableAt ℂ (fun y => B y a c) x) (ξ : Low m → ℂ) :
    g * (uni ξ - 1) = (uni (fderiv ℂ φ x ξ) - 1) * B x
      + uni (φ x) * Matrix.of (fun a c => fderiv ℂ (fun y => B y a c) x ξ) := by
  ext a c
  have h1 : HasFDerivAt (fun y => (g * uni y) a c)
      (∑ b ∈ Finset.univ, g a b • ((lowProj b c).comp (ContinuousLinearMap.id ℂ _))) x := by
    have := HasFDerivAt.sum (u := Finset.univ)
      (fun b _ => (hasFDerivAt_uni_apply (hasFDerivAt_id x) b c).const_mul (g a b))
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp [mul_apply]
  have h2 : HasFDerivAt (fun y => (g * uni y) a c)
      (∑ b ∈ Finset.univ, (uni (φ x) a b • fderiv ℂ (fun y => B y b c) x
        + B x b c • (lowProj a b).comp (fderiv ℂ φ x))) x := by
    have := HasFDerivAt.sum (u := Finset.univ)
      (fun b _ => (hasFDerivAt_uni_apply hφ.hasFDerivAt a b).mul (hBd b c).hasFDerivAt)
    refine this.congr_of_eventuallyEq (hB.mono fun y hy => ?_)
    simp only [hy]
    simp [mul_apply]
  have := congrArg (fun D => D ξ) (h1.unique h2)
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, lowProj_apply, smul_eq_mul] at this
  simp only [Matrix.add_apply, mul_apply, of_apply, this, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun b _ => by ring

theorem upper_mul_upper {m : ℕ} (N P : Matrix (Fin m) (Fin m) ℂ) (hN : ∀ a c : Fin m, c < a → N a c = 0)
    (hP : ∀ a c : Fin m, c < a → P a c = 0) : ∀ a c : Fin m, c < a → (N * P) a c = 0 := by
  intro a c h
  rw [mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  rcases lt_or_ge b a with hb | hb
  · rw [hN a b hb, zero_mul]
  · rw [hP b c (lt_of_lt_of_le h hb), mul_zero]

theorem abs_det_fderiv_flag (m : ℕ) (g : Matrix (Fin m) (Fin m) ℂ) (φ : (Low m → ℂ) → Low m → ℂ)
    (B : (Low m → ℂ) → Matrix (Fin m) (Fin m) ℂ) (x : Low m → ℂ)
    (hB : ∀ᶠ y in 𝓝 x, (B y).BlockTriangular id ∧ g * uni y = uni (φ y) * B y)
    (hdet : IsUnit (B x).det) (hφ : DifferentiableAt ℂ φ x)
    (hBd : ∀ a c, DifferentiableAt ℂ (fun y => B y a c) x) :
    |((fderiv ℂ φ x).restrictScalars ℝ).det| = ∏ s : Low m, ‖B x s.1.1 s.1.1 / B x s.1.2 s.1.2‖ ^ 2 := by
  have hU : IsUnit (uni (φ x)).det := by rw [det_uni]; exact isUnit_one
  have hV : IsUnit (uni x).det := by rw [det_uni]; exact isUnit_one
  have hx := hB.self_of_nhds
  have hTup : ∀ a c : Fin m, c < a → B x a c = 0 := fun a c h => hx.1 h
  have hTi : ∀ a c : Fin m, c < a → (B x)⁻¹ a c = 0 := inv_upper (B x) hTup hdet
  have hTidet : IsUnit (B x)⁻¹.det := (B x).isUnit_nonsing_inv_det hdet
  let D : (Low m → ℂ) → Matrix (Fin m) (Fin m) ℂ :=
    fun ξ => Matrix.of (fun a c => fderiv ℂ (fun y => B y a c) x ξ)
  have hD : ∀ ξ, ∀ a c : Fin m, c < a → D ξ a c = 0 := by
    intro ξ a c h
    have : (fun y => B y a c) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := hB.mono fun y hy => hy.1 h
    simp [D, this.fderiv_eq]
  have hUg : (uni (φ x))⁻¹ * g = B x * (uni x)⁻¹ := by
    have h0 : g * uni x = uni (φ x) * B x := hx.2
    calc (uni (φ x))⁻¹ * g = (uni (φ x))⁻¹ * (g * uni x) * (uni x)⁻¹ := by
          rw [mul_assoc, mul_assoc, mul_nonsing_inv _ hV, mul_one]
      _ = B x * (uni x)⁻¹ := by rw [h0, ← mul_assoc, nonsing_inv_mul _ hU, one_mul]
  have hkey : ∀ ξ, B x * (uni x)⁻¹ * (uni ξ - 1) * (B x)⁻¹
      = (uni (φ x))⁻¹ * (uni (fderiv ℂ φ x ξ) - 1) + D ξ * (B x)⁻¹ := by
    intro ξ
    have h := deriv_flag_eq g φ B x (hB.mono fun y hy => hy.2) hφ hBd ξ
    calc B x * (uni x)⁻¹ * (uni ξ - 1) * (B x)⁻¹
        = (uni (φ x))⁻¹ * (g * (uni ξ - 1)) * (B x)⁻¹ := by rw [← hUg, mul_assoc (uni (φ x))⁻¹]
      _ = _ := by
        rw [h]
        simp only [mul_add, add_mul, ← mul_assoc, nonsing_inv_mul _ hU, one_mul]
        rw [mul_assoc _ (B x), mul_nonsing_inv _ hdet, mul_one]
  let P : Matrix (Low m) (Low m) ℂ := Matrix.of fun s t : Low m =>
    ((1 : Matrix (Fin m) (Fin m) ℂ)⁻¹ * (uni (φ x))⁻¹) s.1.1 t.1.1 * (1 : Matrix (Fin m) (Fin m) ℂ) t.1.2 s.1.2
  let Q : Matrix (Low m) (Low m) ℂ := Matrix.of fun s t : Low m =>
    ((B x)⁻¹⁻¹ * (uni x)⁻¹) s.1.1 t.1.1 * (B x)⁻¹ t.1.2 s.1.2
  have hmain : ∀ ξ, P *ᵥ (fderiv ℂ φ x ξ) = Q *ᵥ ξ := by
    intro ξ
    funext s
    have e := congrFun (congrFun (hkey ξ) s.1.1) s.1.2
    rw [Matrix.add_apply, upper_mul_upper _ _ (hD ξ) hTi _ _ s.2, add_zero] at e
    have e1 : (P *ᵥ (fderiv ℂ φ x ξ)) s
        = ((1 : Matrix (Fin m) (Fin m) ℂ)⁻¹ * (uni (φ x))⁻¹ * (uni (fderiv ℂ φ x ξ) - 1) * (1 : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) s.1.1 s.1.2 := by
      rw [mul_low_mul_apply]; simp only [mulVec, dotProduct, P, of_apply]
    have e2 : (Q *ᵥ ξ) s = ((B x)⁻¹⁻¹ * (uni x)⁻¹ * (uni ξ - 1) * (B x)⁻¹) s.1.1 s.1.2 := by
      rw [mul_low_mul_apply]; simp only [mulVec, dotProduct, Q, of_apply]
    rw [e1, e2, inv_one, one_mul, mul_one, nonsing_inv_nonsing_inv _ hdet, e]
  have hPM : P * LinearMap.toMatrix' ((fderiv ℂ φ x : (Low m → ℂ) →L[ℂ] (Low m → ℂ)) : (Low m → ℂ) →ₗ[ℂ] (Low m → ℂ)) = Q := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun ξ => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec, LinearMap.toMatrix'_mulVec,
      ContinuousLinearMap.coe_coe]
    exact hmain ξ
  have hdetP : P.det = 1 := by
    rw [det_lowConj (φ x) 1 (fun a c h => one_apply_ne h.ne') (by simp)]
    simp
  have hdetQ := det_lowConj x (B x)⁻¹ hTi hTidet
  have hdetL : LinearMap.det ((fderiv ℂ φ x : (Low m → ℂ) →L[ℂ] (Low m → ℂ)) : (Low m → ℂ) →ₗ[ℂ] (Low m → ℂ))
      = ∏ s : Low m, B x s.1.1 s.1.1 / B x s.1.2 s.1.2 := by
    rw [← LinearMap.det_toMatrix']
    have := congrArg Matrix.det hPM
    rw [det_mul, hdetP, one_mul] at this
    rw [this]
    change (Matrix.of fun s t : Low m => ((B x)⁻¹⁻¹ * (uni x)⁻¹) s.1.1 t.1.1 * (B x)⁻¹ t.1.2 s.1.2).det = _
    rw [hdetQ]
    refine Finset.prod_congr rfl fun s _ => ?_
    have hinv : ∀ a, (B x)⁻¹ a a = (B x a a)⁻¹ := fun a => eq_inv_of_mul_eq_one_left (inv_diag_mul _ hTup hdet a)
    rw [hinv, hinv, inv_div_inv]
  have hR : ((fderiv ℂ φ x).restrictScalars ℝ).det = Algebra.norm ℝ (fderiv ℂ φ x).det :=
    LinearMap.det_restrictScalars (f := ((fderiv ℂ φ x : (Low m → ℂ) →L[ℂ] (Low m → ℂ)) : (Low m → ℂ) →ₗ[ℂ] (Low m → ℂ)))
  rw [hR, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity),
    ContinuousLinearMap.det, hdetL, norm_prod, Finset.prod_pow]

end GlobalTheory.FlagFibre
