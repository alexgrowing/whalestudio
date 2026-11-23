import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLevelSetLocalInj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def polyDiff {J : Type} [Fintype J] (p : MvPolynomial J ℂ) (w₀ : J → ℂ) : (J → ℂ) →L[ℂ] ℂ :=
  ∑ j, eval w₀ (pderiv j p) • ContinuousLinearMap.proj j

theorem polyDiff_apply {J : Type} [Fintype J] (p : MvPolynomial J ℂ) (w₀ v : J → ℂ) :
    polyDiff p w₀ v = ∑ j, eval w₀ (pderiv j p) * v j := by
  simp [polyDiff]

theorem hasStrictFDerivAt_eval_poly {J : Type} [Fintype J] (p : MvPolynomial J ℂ) (w₀ : J → ℂ) :
    HasStrictFDerivAt (fun w => eval w p) (polyDiff p w₀) w₀ := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h0 : polyDiff (C a) w₀ = 0 := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [polyDiff_apply]
    rw [h0]
    simp only [eval_C]
    exact hasStrictFDerivAt_const a w₀
  | add p q hp hq =>
    have h0 : polyDiff (p + q) w₀ = polyDiff p w₀ + polyDiff q w₀ := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [polyDiff_apply, add_mul, Finset.sum_add_distrib]
    rw [h0]
    simp only [map_add]
    exact hp.add hq
  | mul_X p n hp =>
    have hX : HasStrictFDerivAt (fun w : J → ℂ => w n)
        (ContinuousLinearMap.proj n : (J → ℂ) →L[ℂ] ℂ) w₀ :=
      hasStrictFDerivAt_apply n w₀
    have h := hp.mul hX
    have h0 : polyDiff (p * X n) w₀ =
        eval w₀ p • (ContinuousLinearMap.proj n : (J → ℂ) →L[ℂ] ℂ) + w₀ n • polyDiff p w₀ := by
      have key : ∀ j, eval w₀ (pderiv j (X n : MvPolynomial J ℂ)) = if j = n then 1 else 0 := by
        intro j
        by_cases hj : j = n
        · subst hj
          simp
        · simp [pderiv_X_of_ne (Ne.symm hj), hj]
      refine ContinuousLinearMap.ext fun v => ?_
      have s1 : ∑ j, eval w₀ p * (if j = n then (1 : ℂ) else 0) * v j = eval w₀ p * v n := by
        simp
      have s2 : ∑ j, eval w₀ (pderiv j p) * w₀ n * v j = w₀ n * ∑ j, eval w₀ (pderiv j p) * v j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp only [polyDiff_apply, pderiv_mul, map_add, map_mul, key, eval_X, add_mul,
        Finset.sum_add_distrib, s1, s2, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
      ring
    rw [h0]
    simp only [map_mul, eval_X]
    exact h

theorem polyDiff_pi_range_eq_top {J R : Type} [Fintype J] [Fintype R] (f : R → MvPolynomial J ℂ)
    (w₀ : J → ℂ) (hli : LinearIndependent ℂ (fun i => fun j => eval w₀ (pderiv j (f i)))) :
    LinearMap.range ((ContinuousLinearMap.pi fun i => polyDiff (f i) w₀ : (J → ℂ) →L[ℂ] (R → ℂ)) :
      (J → ℂ) →ₗ[ℂ] (R → ℂ)) = ⊤ := by
  classical
  let M : Matrix R J ℂ := Matrix.of fun i j => eval w₀ (pderiv j (f i))
  have hrank : M.rank = Fintype.card R := LinearIndependent.rank_matrix (M := M) hli
  have hLM : ((ContinuousLinearMap.pi fun i => polyDiff (f i) w₀ : (J → ℂ) →L[ℂ] (R → ℂ)) :
      (J → ℂ) →ₗ[ℂ] (R → ℂ)) = M.mulVecLin := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [polyDiff_apply, M, Matrix.mulVec, dotProduct]
  rw [hLM]
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← hrank, Matrix.rank]

theorem exists_prod_bijective {J R : Type} [Fintype J] [Fintype R] (L : (J → ℂ) →ₗ[ℂ] (R → ℂ))
    (hL : LinearMap.range L = ⊤) (m : ℕ) (hm : m + Fintype.card R = Fintype.card J) :
    ∃ π : (J → ℂ) →ₗ[ℂ] (Fin m → ℂ),
      LinearMap.ker (L.prod π) = ⊥ ∧ LinearMap.range (L.prod π) = ⊤ := by
  have hK : Module.finrank ℂ (LinearMap.ker L) = m := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [hL, finrank_top, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card] at h
    omega
  obtain ⟨C, hC⟩ := (LinearMap.ker L).exists_isCompl
  have hKm : Module.finrank ℂ (LinearMap.ker L) = Module.finrank ℂ (Fin m → ℂ) := by
    rw [hK, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e : LinearMap.ker L ≃ₗ[ℂ] (Fin m → ℂ) := LinearEquiv.ofFinrankEq _ _ hKm
  let π : (J → ℂ) →ₗ[ℂ] (Fin m → ℂ) := e.toLinearMap ∘ₗ (LinearMap.ker L).projectionOnto C hC
  have hker : LinearMap.ker (L.prod π) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : L x = 0 := congrArg Prod.fst hx
    have h2 : π x = 0 := congrArg Prod.snd hx
    have hxK : x ∈ LinearMap.ker L := h1
    have h3 : (LinearMap.ker L).projectionOnto C hC x = ⟨x, hxK⟩ :=
      Submodule.projectionOnto_apply_of_mem_left hC hxK
    have h4 : e ⟨x, hxK⟩ = 0 := by
      have : π x = e ((LinearMap.ker L).projectionOnto C hC x) := rfl
      rw [this, h3] at h2
      exact h2
    have h5 : (⟨x, hxK⟩ : LinearMap.ker L) = 0 := (LinearEquiv.map_eq_zero_iff e).1 h4
    exact congrArg Subtype.val h5
  refine ⟨π, hker, ?_⟩
  rw [LinearMap.range_eq_top, ← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  · exact LinearMap.ker_eq_bot.1 hker
  · rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega

theorem LevelSetLocalInj.proof : LevelSetLocalInj.Statement := by
  intro J _ R _ f w₀ hli m hm
  let F : (J → ℂ) → (R → ℂ) := fun w i => eval w (f i)
  let L : (J → ℂ) →L[ℂ] (R → ℂ) := ContinuousLinearMap.pi fun i => polyDiff (f i) w₀
  have hF : HasStrictFDerivAt F L w₀ :=
    hasStrictFDerivAt_pi.2 fun i => hasStrictFDerivAt_eval_poly (f i) w₀
  obtain ⟨πl, hker, hran⟩ :=
    exists_prod_bijective (L : (J → ℂ) →ₗ[ℂ] (R → ℂ)) (polyDiff_pi_range_eq_top f w₀ hli) m hm
  let π : (J → ℂ) →L[ℂ] (Fin m → ℂ) := LinearMap.toContinuousLinearMap πl
  let Φ : (J → ℂ) →L[ℂ] (R → ℂ) × (Fin m → ℂ) := L.prod π
  let E := ContinuousLinearEquiv.ofBijective Φ hker hran
  let G : (J → ℂ) → (R → ℂ) × (Fin m → ℂ) := fun w => (F w, π w)
  have hG : HasStrictFDerivAt G (E : (J → ℂ) →L[ℂ] (R → ℂ) × (Fin m → ℂ)) w₀ :=
    (hF.prodMk π.hasStrictFDerivAt).congr_fderiv (ContinuousLinearEquiv.coe_ofBijective Φ hker hran).symm
  refine ⟨(hG.toOpenPartialHomeomorph G).source, (hG.toOpenPartialHomeomorph G).open_source,
    hG.mem_toOpenPartialHomeomorph_source, π, ?_⟩
  rintro x ⟨hxU, hx⟩ y ⟨hyU, hy⟩ hxy
  apply (hG.toOpenPartialHomeomorph G).injOn hxU hyU
  rw [hG.toOpenPartialHomeomorph_coe]
  exact Prod.ext (funext fun i => (hx i).trans (hy i).symm) hxy

end GroundTheory.Heights₂.Heights.LowerBoundFree
