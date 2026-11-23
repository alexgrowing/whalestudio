import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceStatements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

theorem rpow_third_le {t : ℝ} (ht : 0 < t) (hℓ : Real.exp 1 ≤ ell t) (n : ℕ) :
    t ^ (1 / 3 : ℝ) ≤ 2 * (Real.log (ell t) ^ n / ell t) := by
  have hℓ1 : 1 ≤ ell t := (Real.one_le_exp zero_le_one).trans hℓ
  have hℓ0 : 0 < ell t := by linarith
  have hlog : Real.log t = -ell t := by
    rw [ell, Real.log_inv, neg_neg]
  have hL : 1 ≤ Real.log (ell t) := by
    have := Real.log_le_log (Real.exp_pos 1) hℓ
    rwa [Real.log_exp] at this
  have hLn : 1 ≤ Real.log (ell t) ^ n := one_le_pow₀ hL
  have hq := Real.quadratic_le_exp_of_nonneg (x := ell t / 3) (by positivity)
  have hE0 : 0 < Real.exp (ell t / 3) := Real.exp_pos _
  have hE : ell t ≤ 2 * Real.exp (ell t / 3) := by nlinarith [sq_nonneg (ell t - 3 / 2)]
  have h1 : t ^ (1 / 3 : ℝ) = (Real.exp (ell t / 3))⁻¹ := by
    rw [Real.rpow_def_of_pos ht, hlog, ← Real.exp_neg]
    congr 1
    ring
  rw [h1, inv_eq_one_div, div_le_iff₀ hE0]
  have h2 : 1 ≤ 2 * Real.exp (ell t / 3) / ell t := by
    rw [le_div_iff₀ hℓ0]
    linarith
  calc (1 : ℝ) ≤ 2 * Real.exp (ell t / 3) / ell t := h2
    _ ≤ 2 * Real.exp (ell t / 3) / ell t * Real.log (ell t) ^ n :=
        le_mul_of_one_le_right (by positivity) hLn
    _ = 2 * (Real.log (ell t) ^ n / ell t) * Real.exp (ell t / 3) := by ring

theorem Convergence.proof (hW : WeightCocycle.Statement) : Convergence.Statement := by
  intro X _ _ _ _ _ D A F a a₀ δ Λ M CE L₀ ha hδ hL hM hCE hTV
  obtain ⟨C', ℓ₁, hT⟩ := TelescopingFamily.proof D A F Λ
  refine ⟨(D + 1) * (C' ^ 2 * M + 2 * |C'| * M + |C'| * CE) / δ, max (max L₀ ℓ₁) (Real.exp 1),
    fun x hx t t' ht' htt hl => ?_⟩
  have hl0 : L₀ ≤ ell t := (le_max_left _ _).trans ((le_max_left _ _).trans hl)
  have hl1 : ℓ₁ ≤ ell t := (le_max_right _ _).trans ((le_max_left _ _).trans hl)
  have hle : Real.exp 1 ≤ ell t := (le_max_right _ _).trans hl
  have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hℓ0 : 0 < ell t := by linarith
  have ht : 0 < t := ht'.trans_le htt
  have hA : F.Admissible t := ⟨ht, fun i => (hL i).trans hl0⟩
  have hA' : F.Admissible t' := ⟨ht', fun i => ((hL i).trans hl0).trans (ell_anti ht' htt)⟩
  have hc : ∑ i, |x (some i)| ≤ Λ := by
    refine le_trans ?_ hx
    rw [Fintype.sum_option]
    linarith [abs_nonneg (x none)]
  have hu0 : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
  have hL1 : 1 ≤ Real.log (ell t) := by
    have := Real.log_le_log (Real.exp_pos 1) hle
    rwa [Real.log_exp] at this
  obtain ⟨aN, haN⟩ : ∃ aN : ℝ,
      aN = |C'| * t ^ (1 / 3 : ℝ) + C' ^ 2 * (Real.log (ell t) / ell t) := ⟨_, rfl⟩
  have haN0 : 0 ≤ aN := by
    rw [haN]
    have : 0 ≤ Real.log (ell t) / ell t := div_nonneg (by linarith) hℓ0.le
    positivity
  obtain ⟨f, hf⟩ : ∃ f : X → ℝ, f = fun p => F.coefWeight x t p - F.coefWeight x t' p := ⟨_, rfl⟩
  have hfeq : ∀ p, f p = ∑ i, x (some i) * ((F.sys i).ph t p - (F.sys i).ph t' p) := by
    intro p
    simp only [hf, Family.coefWeight, mul_sub, Finset.sum_sub_distrib]
  have hnear : ∀ p ∈ F.Yo, F.r p ≤ ell t → |f p| ≤ aN := by
    intro p hp hr
    rw [hfeq]
    refine ((hT (fun i => x (some i)) hc t t' ht' htt hl1 p hp).1 hr).trans ?_
    have hCu : C' * t ^ (1 / 3 : ℝ) ≤ |C'| * t ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self C') hu0
    have e : C' * (t ^ (1 / 3 : ℝ) + errE C' t) =
        C' * t ^ (1 / 3 : ℝ) + C' ^ 2 * (Real.log (ell t) / ell t) := by
      rw [errE]
      ring
    rw [e, haN]
    linarith
  have hfar : ∀ p ∈ F.Yo, ell t < F.r p → |f p| ≤ |C'| * Real.log (F.r p) := by
    intro p hp hr
    rw [hfeq]
    refine ((hT (fun i => x (some i)) hc t t' ht' htt hl1 p hp).2 hr).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self C') (Real.log_nonneg (by linarith))
  have hfc : Continuous f := by
    rw [hf]
    refine Continuous.sub ?_ ?_ <;>
      refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    · exact ReciprocityTheory.AnForm.M.PLAux.smooth_continuous ((F.sys i).smooth t ht (hA.2 i))
    · exact ReciprocityTheory.AnForm.M.PLAux.smooth_continuous ((F.sys i).smooth t' ht' (hA'.2 i))
  have hterm : ∀ k ∈ Finset.range (D + 1), |mInt A (F.mixedProduct a x t t' k) f| ≤
      aN * M + |C'| * (CE * Real.log (ell t) ^ (D + 1) / ell t) := by
    intro k hk
    have hkD : k ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hΦ := F.mixedProduct_isPotential ha x hA hA' k
    exact ConvergenceSigned.proof A _ hΦ F.Yo F.r M CE (hTV x hx t t' ht' htt hl0 k hkD) f
      hfc.measurable (ReciprocityTheory.AnForm.M.mIntegrableCont A _ hΦ f hfc) aN |C'| (ell t) haN0
      (abs_nonneg _) hle hnear hfar
  have hsum := hW D A F a ha x t t' hA hA'
  rw [← hf] at hsum
  have hdiff : F.arithSelfInt a a₀ δ x t - F.arithSelfInt a a₀ δ x t' =
      (∑ k ∈ Finset.range (D + 1), mInt A (F.mixedProduct a x t t' k) f) / δ := by
    rw [← hsum]
    unfold Family.arithSelfInt
    ring
  rw [hdiff, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
  have hP : 0 ≤ Real.log (ell t) / ell t := div_nonneg (by linarith) hℓ0.le
  have hQ : 0 ≤ Real.log (ell t) ^ (D + 1) / ell t := by positivity
  have hu2 := rpow_third_le ht hle (D + 1)
  have hC0 : 0 ≤ |C'| := abs_nonneg C'
  have key : aN * M + |C'| * (CE * Real.log (ell t) ^ (D + 1) / ell t) ≤
      (C' ^ 2 * M + 2 * |C'| * M + |C'| * CE) *
        (Real.log (ell t) / ell t + Real.log (ell t) ^ (D + 1) / ell t) := by
    rw [haN, mul_div_assoc CE]
    nlinarith [mul_nonneg (mul_nonneg hC0 hM) (sub_nonneg.2 hu2), mul_nonneg (sq_nonneg C') hM,
      mul_nonneg (mul_nonneg (sq_nonneg C') hM) hQ, mul_nonneg (mul_nonneg hC0 hM) hP,
      mul_nonneg (mul_nonneg hC0 hCE) hP, mul_nonneg (mul_nonneg hC0 hM) hQ]
  have e2 : convRate D ((D + 1) * (C' ^ 2 * M + 2 * |C'| * M + |C'| * CE) / δ) t * δ =
      (D + 1) * ((C' ^ 2 * M + 2 * |C'| * M + |C'| * CE) *
        (Real.log (ell t) / ell t + Real.log (ell t) ^ (D + 1) / ell t)) := by
    unfold convRate
    field_simp
  rw [e2]
  calc |∑ k ∈ Finset.range (D + 1), mInt A (F.mixedProduct a x t t' k) f|
      ≤ ∑ k ∈ Finset.range (D + 1), |mInt A (F.mixedProduct a x t t' k) f| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (D + 1),
          (aN * M + |C'| * (CE * Real.log (ell t) ^ (D + 1) / ell t)) :=
        Finset.sum_le_sum hterm
    _ = (D + 1) * (aN * M + |C'| * (CE * Real.log (ell t) ^ (D + 1) / ell t)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)

def evalLin (σ : Type*) (N : ℕ) :
    MvPolynomial.restrictTotalDegree σ ℝ N →ₗ[ℝ] ((σ → ℝ) → ℝ) where
  toFun p x := MvPolynomial.eval x p.1
  map_add' p q := by
    funext x
    simp
  map_smul' c p := by
    funext x
    simp [MvPolynomial.smul_eval]

theorem evalLin_injective (σ : Type*) (N : ℕ) : Function.Injective (evalLin σ N) :=
  fun _ _ h => Subtype.ext (MvPolynomial.funext fun x => congrFun h x)

theorem CoefficientLimit.proof (hW : WeightCocycle.Statement)
    (hPol : PolynomialInWeights.Statement) : CoefficientLimit.Statement := by
  classical
  intro X _ _ _ _ _ D A F a a₀ δ L₀ ha ha₀ hδ hL hTV
  have hlim : ∀ x : Option (Fin F.m) → ℝ,
      ∃ y, Tendsto (fun t => F.arithSelfInt a a₀ δ x t) (𝓝[>] 0) (𝓝 y) := by
    intro x
    obtain ⟨M, CE, hM, hCE, hT⟩ := hTV (∑ o, |x o|)
    obtain ⟨C, L₁, hC⟩ :=
      Convergence.proof hW D A F a a₀ δ (∑ o, |x o|) M CE L₀ ha hδ hL hM hCE hT
    obtain ⟨y, hy, -⟩ := ConvergenceRate.proof D (fun t => F.arithSelfInt a a₀ δ x t) C L₁
      fun t t' h1 h2 h3 => hC x le_rfl t t' h1 h2 h3
    exact ⟨y, hy⟩
  choose g hg using hlim
  have hadm : ∀ᶠ t in 𝓝[>] (0 : ℝ), F.Admissible t := by
    filter_upwards [self_mem_nhdsWithin, tendsto_ell.eventually_ge_atTop L₀] with t ht hl
    exact ⟨ht, fun i => (hL i).trans hl⟩
  let V := MvPolynomial.restrictTotalDegree (Option (Fin F.m)) ℝ (D + 1)
  let ev := evalLin (Option (Fin F.m)) (D + 1)
  let W := LinearMap.range ev
  have hWc : IsClosed (W : Set ((Option (Fin F.m) → ℝ) → ℝ)) :=
    Submodule.closed_of_finiteDimensional W
  have ha₀V : a₀ ∈ V := (MvPolynomial.mem_restrictTotalDegree (m := D + 1) (p := a₀)).2 ha₀
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), (fun x => F.arithSelfInt a a₀ δ x t) ∈ W := by
    filter_upwards [hadm] with t ht
    obtain ⟨q, hq, hqe⟩ := hPol D A F a ha t ht
    have hqV : q ∈ V := (MvPolynomial.mem_restrictTotalDegree (m := D + 1) (p := q)).2 hq
    refine ⟨⟨δ⁻¹ • (a₀ + q), V.smul_mem _ (V.add_mem ha₀V hqV)⟩, ?_⟩
    funext x
    show MvPolynomial.eval x (δ⁻¹ • (a₀ + q)) = F.arithSelfInt a a₀ δ x t
    rw [MvPolynomial.smul_eval, MvPolynomial.eval_add, hqe, Family.arithSelfInt, div_eq_inv_mul]
  have htend : Tendsto (fun t => fun x => F.arithSelfInt a a₀ δ x t) (𝓝[>] 0) (𝓝 g) :=
    tendsto_pi_nhds.2 hg
  have hgW : g ∈ W := hWc.mem_of_tendsto htend hmem
  obtain ⟨P', hP'⟩ := LinearMap.mem_range.1 hgW
  have hevalP : ∀ x, MvPolynomial.eval x P'.1 = g x := fun x => congrFun hP' x
  refine ⟨P'.1, (MvPolynomial.mem_restrictTotalDegree (m := D + 1) (p := P'.1)).1 P'.2, fun x => ?_, fun p hp α => ?_⟩
  · rw [hevalP]
    exact hg x
  · let e := LinearEquiv.ofInjective ev (evalLin_injective _ _)
    let ψ : W →ₗ[ℝ] ℝ := (MvPolynomial.lcoeff ℝ α) ∘ₗ V.subtype ∘ₗ e.symm.toLinearMap
    have hψ : Continuous ψ := LinearMap.continuous_of_finiteDimensional ψ
    have hψe : ∀ v : V, ψ (e v) = (v : MvPolynomial (Option (Fin F.m)) ℝ).coeff α := by
      intro v
      simp [ψ]
    let G : ℝ → W := fun t =>
      if h : (fun x => F.arithSelfInt a a₀ δ x t) ∈ W then ⟨_, h⟩ else 0
    have hG : Tendsto G (𝓝[>] 0) (𝓝 (e P')) := by
      rw [tendsto_subtype_rng]
      have he : ((e P' : W) : (Option (Fin F.m) → ℝ) → ℝ) = g := by
        rw [LinearEquiv.ofInjective_apply]
        exact hP'
      rw [he]
      refine htend.congr' ?_
      filter_upwards [hmem] with t ht
      show _ = ((G t : W) : (Option (Fin F.m) → ℝ) → ℝ)
      simp only [G, dif_pos ht]
    have hlimψ := (hψ.tendsto _).comp hG
    rw [hψe] at hlimψ
    refine hlimψ.congr' ?_
    filter_upwards [hp, hmem] with t hpt ht
    have hpV : p t ∈ V := (MvPolynomial.mem_restrictTotalDegree (m := D + 1) (p := p t)).2 hpt.1
    have hGt : G t = e ⟨p t, hpV⟩ := by
      apply Subtype.ext
      rw [LinearEquiv.ofInjective_apply]
      simp only [G, dif_pos ht]
      funext x
      exact (hpt.2 x).symm
    simp only [Function.comp_apply, hGt, hψe]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
