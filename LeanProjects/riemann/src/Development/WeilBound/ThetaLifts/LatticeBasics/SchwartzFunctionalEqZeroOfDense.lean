import Mathlib
import Development.WeilBound.ThetaLifts.SchwartzMoments.EqZeroOfMoments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

noncomputable section

namespace GlobalTheory.ThK.Dbl.Dense

open PositivityTheory.ThKOwn (polE eq_zero_PG)

theorem exp_tg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : E → ℝ}
    (hr : r.HasTemperateGrowth) (c : ℂ) (s : ℝ) :
    (fun y => c * Complex.exp ((s : ℂ) * Complex.I * (r y : ℂ))).HasTemperateGrowth := by
  have hlin : (fun y => (s / (2 * Real.pi)) * r y).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul hr
  have hc := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp hlin
  have h : (fun y => c * Complex.exp ((s : ℂ) * Complex.I * (r y : ℂ))) =
      fun y => c * ((GlobalTheory.Published.Metaplectic.eChar : ℝ → ℂ) ∘ fun y => (s / (2 * Real.pi)) * r y) y := by
    funext y
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [Function.comp, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 2
    push_cast
    field_simp
  rw [h]
  exact (Function.HasTemperateGrowth.const c).mul hc

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem quad_tg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E ≃L[ℝ] V)
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : (fun x => Q (L x) (L x)).HasTemperateGrowth := by
  have hL : (fun x => L x).HasTemperateGrowth := (L : E →L[ℝ] V).hasTemperateGrowth
  exact (Q.toContinuousBilinearMap).bilinear_hasTemperateGrowth hL hL

theorem lower_bound {n : ℕ} (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] V) (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hpos : ∀ x, x ≠ 0 → 0 < Q x x) :
    ∃ w : ℝ, 0 < w ∧ ∀ x, w * ‖x‖ ^ 2 ≤ Q (L x) (L x) := by
  set q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Q (L x) (L x) with hqdef
  have hq : Continuous q := (quad_tg L Q).1.continuous
  have hscale : ∀ (t : ℝ) x, q (t • x) = t ^ 2 * q x := by
    intro t x
    simp only [hqdef, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hq0 : q 0 = 0 := by simp [hqdef]
  by_cases hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMinOn hne
      hq.continuousOn
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    have hw : 0 < q u := hpos _ (by simpa using hu0)
    refine ⟨q u, hw, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      show _ ≤ q 0
      simp [hq0]
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hm : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simp [norm_smul, hn]
    have h1 : q u ≤ q (‖x‖⁻¹ • x) := hmin hm
    have h2 : q x = ‖x‖ ^ 2 * q (‖x‖⁻¹ • x) := by
      rw [hscale]
      field_simp
    show _ ≤ q x
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x = 0 := by
      by_contra hx
      exact hne ⟨‖x‖⁻¹ • x, by simp [norm_smul, norm_ne_zero_iff.2 hx]⟩
    subst hx
    show _ ≤ q 0
    simp [hq0]

theorem poly_mem {n : ℕ} (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] V)
    (N : Submodule ℂ (SchwartzMap V ℂ))
    (hmul : ∀ (l : V →ₗ[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (l x : ℂ) * f x) → f₁ ∈ N)
    (f₀ : SchwartzMap V ℂ) (hf₀ : f₀ ∈ N) (P : MvPolynomial (Fin n) ℂ) :
    ∃ F ∈ N, ∀ y, F y = polE P (L.symm y) * f₀ y := by
  induction P using MvPolynomial.induction_on with
  | C z => exact ⟨z • f₀, N.smul_mem z hf₀, fun y => by simp [polE]⟩
  | add P R hP hR =>
    obtain ⟨F, hF, hFy⟩ := hP
    obtain ⟨G, hG, hGy⟩ := hR
    refine ⟨F + G, N.add_mem hF hG, fun y => ?_⟩
    have h : polE (P + R) (L.symm y) = polE P (L.symm y) + polE R (L.symm y) := by simp [polE]
    rw [h, add_mul, SchwartzMap.add_apply, hFy, hGy]
  | mul_X P p hP =>
    obtain ⟨F, hF, hFy⟩ := hP
    let l : V →L[ℝ] ℝ := (EuclideanSpace.proj (𝕜 := ℝ) p).comp (L.symm : V →L[ℝ] EuclideanSpace ℝ (Fin n))
    have hg : (fun y => ((l y : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp l).hasTemperateGrowth
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun y => ((l y : ℝ) : ℂ)) F,
      hmul (l : V →ₗ[ℝ] ℝ) F _ hF (fun y => ?_), fun y => ?_⟩
    · rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
      rfl
    · rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hFy]
      have h : polE (P * MvPolynomial.X p) (L.symm y) = polE P (L.symm y) * ((l y : ℝ) : ℂ) := by
        simp [polE, l]
      rw [h]
      ring

theorem schwartz_functional_eq_zero_of_dense (Q Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (c₀ : ℂ)
    (f₀ : SchwartzMap V ℂ) (hc : c₀ ≠ 0) (hpos : ∀ x, x ≠ 0 → 0 < Q x x)
    (hf : ∀ x, f₀ x = c₀ * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ)))
    (N : Submodule ℂ (SchwartzMap V ℂ)) (hN : f₀ ∈ N)
    (hmul : ∀ (l : V →ₗ[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (l x : ℂ) * f x) → f₁ ∈ N)
    (T : SchwartzMap V ℂ →L[ℂ] ℂ) (hT : ∀ f ∈ N, T f = 0) : T = 0 := by
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃L[ℝ] V := (toEuclidean (E := V)).symm
  let q : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℝ := fun x => Q (L x) (L x)
  let r : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℝ := fun x => Q' (L x) (L x)
  have hq : q.HasTemperateGrowth := quad_tg L Q
  have hr : r.HasTemperateGrowth := quad_tg L Q'
  obtain ⟨w, hw, hlow⟩ := lower_bound L Q hpos
  let g : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ :=
    fun y => c₀ * Complex.exp (((-1 : ℝ) : ℂ) * Complex.I * (r y : ℂ))
  let g' : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ :=
    fun y => c₀⁻¹ * Complex.exp (((1 : ℝ) : ℂ) * Complex.I * (r y : ℂ))
  have hg : g.HasTemperateGrowth := exp_tg hr c₀ (-1)
  have hg' : g'.HasTemperateGrowth := exp_tg hr c₀⁻¹ 1
  let A : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ →L[ℂ] SchwartzMap V ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
  let B : SchwartzMap V ℂ →L[ℂ] SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L
  let M := SchwartzMap.smulLeftCLM ℂ g
  let M' := SchwartzMap.smulLeftCLM ℂ g'
  have hS : ∀ f, T (A (M f)) = 0 := by
    have hext := eq_zero_PG q hq w hw hlow (T ∘L A ∘L M)
      (fun f hf' => by
        obtain ⟨P, hP⟩ := hf'
        obtain ⟨F, hFN, hF⟩ := poly_mem L N hmul f₀ hN P
        have hAM : A (M f) = F := by
          ext y
          have hy : (L (L.symm y)) = y := L.apply_symm_apply y
          simp only [A, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp,
            M, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hP, hF, hf]
          simp only [g, q, r, hy]
          push_cast
          rw [show -(Q y y : ℂ) - Complex.I * (Q' y y : ℂ) =
            -1 * Complex.I * (Q' y y : ℂ) + -(Q y y : ℂ) by ring, Complex.exp_add]
          ring
        show T (A (M f)) = 0
        rw [hAM]
        exact hT F hFN)
    exact fun f => DFunLike.congr_fun hext f
  ext h
  have hinv : A (M (M' (B h))) = h := by
    ext y
    simp only [A, B, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp,
      M, M', SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg',
      smul_eq_mul, L.apply_symm_apply]
    simp only [g, g']
    rw [← mul_assoc, mul_mul_mul_comm, ← Complex.exp_add]
    push_cast
    simp [hc]
  rw [← hinv]
  simpa using hS _

end GlobalTheory.ThK.Dbl.Dense

end
