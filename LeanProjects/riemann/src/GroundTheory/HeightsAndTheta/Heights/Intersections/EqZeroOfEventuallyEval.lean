import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExMapAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StRatioAlgDep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem pointFormRank_holds.exists_surj_coords {σ : Type*} {n : ℕ} (ℓ : σ → (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hℓ : ∀ x, (∀ s, ℓ s x = 0) → x = 0) :
    ∀ m, m ≤ n → ∃ q : Fin m → σ, Function.Surjective (fun x : Fin n → ℂ => fun j => ℓ (q j) x) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨Fin.elim0, fun t => ⟨0, funext fun j => j.elim0⟩⟩
  | succ m ih =>
    intro hm
    obtain ⟨q, hq⟩ := ih (by omega)
    let Φ : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) := LinearMap.pi fun j => ℓ (q j)
    have hrank := LinearMap.finrank_range_add_finrank_ker Φ
    have hle : Module.finrank ℂ (LinearMap.range Φ) ≤ m := by
      simpa using Submodule.finrank_le (LinearMap.range Φ)
    have hpos : 0 < Module.finrank ℂ (LinearMap.ker Φ) := by
      rw [Module.finrank_fin_fun] at hrank; omega
    obtain ⟨⟨x, hxk⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hΦx : ∀ j, ℓ (q j) x = 0 := fun j => congr_fun (LinearMap.mem_ker.mp hxk) j
    obtain ⟨s, hs⟩ : ∃ s, ℓ s x ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (hℓ x h)
    refine ⟨Fin.snoc q s, fun t => ?_⟩
    obtain ⟨x0, hx0'⟩ := hq (Fin.init t)
    refine ⟨x0 + ((t (Fin.last m) - ℓ s x0) / ℓ s x) • x, funext fun j => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last, map_add, map_smul, smul_eq_mul]
      rw [div_mul_cancel₀ _ hs]
      ring
    · simp only [Fin.snoc_castSucc, map_add, map_smul, hΦx, smul_eq_mul, mul_zero, add_zero]
      exact congr_fun hx0' j

theorem pointFormRank_holds.eq_zero_of_eventually_eval {d : ℕ} (f : MvPolynomial (Fin d) ℂ) (a : Fin d → ℂ)
    (h : ∀ᶠ z in 𝓝 a, eval z f = 0) : f = 0 := by
  have han : AnalyticOnNhd ℂ (fun z => eval z f) Set.univ := AnalyticOnNhd.eval_mvPolynomial f
  have h0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h
  exact MvPolynomial.funext fun z => by simpa using h0 (Set.mem_univ z)

theorem pointFormRank_holds.proof (hA : RatioAlgDep.Statement) : pointFormRank_holds.Statement := by
  intro K _ ι _ Q d n F y hQ hdn hF hev
  classical
  have hy : F y ∈ mcPts Q := hev.self_of_nhds
  choose c hc using hy.1
  have hcomp : ∀ p, AnalyticAt ℂ (fun y' => F y' p) y := analyticAt_pi_iff.mp hF
  have hDy : ∀ p : Σ k, ι k, F y ⟨p.1, c p.1⟩ ≠ 0 := fun p => hc p.1
  set r : (Σ k, ι k) → (Fin n → ℂ) → ℂ := fun p y' => F y' p / F y' ⟨p.1, c p.1⟩ with hr_def
  have hr : ∀ p, AnalyticAt ℂ (r p) y := fun p => (hcomp p).div (hcomp _) (hDy p)
  have hnear : ∀ᶠ y' in 𝓝 y, ∀ k, F y' ⟨k, c k⟩ ≠ 0 :=
    Filter.eventually_all.mpr fun k => (hcomp ⟨k, c k⟩).continuousAt.eventually_ne (hc k)
  set F' := fderiv ℂ F y with hF'_def
  have hF' : HasFDerivAt F F' y := hF.differentiableAt.hasFDerivAt
  set ℓ : (Σ k, ι k) → (Fin n → ℂ) →L[ℂ] ℂ := fun p => fderiv ℂ (r p) y with hℓ_def
  have hℓ : ∀ p, HasFDerivAt (r p) (ℓ p) y := fun p => (hr p).differentiableAt.hasFDerivAt
  have hprod : ∀ p, HasFDerivAt (fun y' => r p y' * F y' ⟨p.1, c p.1⟩)
      (r p y • (ContinuousLinearMap.proj ⟨p.1, c p.1⟩).comp F' + F y ⟨p.1, c p.1⟩ • ℓ p) y :=
    fun p => (hℓ p).mul (hasFDerivAt_pi'.mp hF' _)
  have heq : ∀ p, (fun y' => F y' p) =ᶠ[𝓝 y] fun y' => r p y' * F y' ⟨p.1, c p.1⟩ :=
    fun p => hnear.mono fun y' hy' => (div_mul_cancel₀ _ (hy' p.1)).symm
  have hderiv : ∀ p, (ContinuousLinearMap.proj p).comp F' =
      r p y • (ContinuousLinearMap.proj ⟨p.1, c p.1⟩).comp F' + F y ⟨p.1, c p.1⟩ • ℓ p :=
    fun p => (hasFDerivAt_pi'.mp hF' p).unique ((hprod p).congr_of_eventuallyEq (heq p))
  by_contra hno
  push Not at hno
  have hinj : ∀ x, (∀ p, ℓ p x = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    refine hno x hx0 (fun k => F' x ⟨k, c k⟩ / F y ⟨k, c k⟩) ?_
    funext p
    have h1 := congrArg (fun L => L x) (hderiv p)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, FunLike.coe_add, Pi.add_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hx p, mul_zero, add_zero] at h1
    rw [h1, bsmul, hr_def]
    ring
  obtain ⟨q, hq⟩ := pointFormRank_holds.exists_surj_coords (fun p => (ℓ p).toLinearMap)
    (fun x hx => hinj x (by simpa using hx)) d hdn
  have hg : HasStrictFDerivAt (fun y' j => r (q j) y') (ContinuousLinearMap.pi fun j => ℓ (q j)) y :=
    hasStrictFDerivAt_pi.mpr fun j => (hr (q j)).hasStrictFDerivAt
  have hrange : (ContinuousLinearMap.pi fun j => ℓ (q j) : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)).range = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun t => ?_
    obtain ⟨x, hx⟩ := hq t
    exact ⟨x, hx⟩
  have hmap := hg.map_nhds_eq_of_surj hrange
  obtain ⟨f, hf0, hfz⟩ := hA K ι Q d c q hQ
  have hev' : ∀ᶠ y' in 𝓝 y, eval (fun j => r (q j) y') (map (Int.castRingHom ℂ) f) = 0 := by
    filter_upwards [hev, hnear] with y' hy' hy'c
    exact hfz (F y') hy'.2 hy'c
  have hz : ∀ᶠ z in 𝓝 ((fun y' j => r (q j) y') y), eval z (map (Int.castRingHom ℂ) f) = 0 := by
    rw [← hmap]
    exact Filter.eventually_map.mpr hev'
  have h0 := pointFormRank_holds.eq_zero_of_eventually_eval _ _ hz
  exact hf0 (MvPolynomial.map_injective _ (Int.castRingHom ℂ).injective_int (h0.trans (map_zero _).symm))

end GroundTheory.Heights₂.Heights.Inter
