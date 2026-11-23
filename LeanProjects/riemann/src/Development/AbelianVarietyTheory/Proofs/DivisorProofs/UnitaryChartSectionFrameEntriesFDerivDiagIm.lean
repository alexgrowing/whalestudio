import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

theorem yF_expand {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (w : V (nd X)) (τ : X.Ψ) (k j : Fin r) :
    yF X w τ k j = (∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m j) + gsB X w τ k j := by
  simp only [yF, yM, Matrix.mul_apply, mat, Matrix.of_apply]
  have hk : gsB X w τ k j = ∑ m, if k = m then gsB X w τ m j else 0 := by simp
  rw [Finset.sum_filter, hk, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rcases lt_trichotomy m k with h | h | h
  · simp [h, h.ne']
  · subst h; simp [nmat]
  · have h1 : ¬ m < k := not_lt.2 h.le
    have h2 : k ≠ m := h.ne
    simp [nmat, h1, h2]

theorem diagreal {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (_hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (a : Fin r) :
    (dY X z τ a a).im = 0 := by
  by_cases hd : DifferentiableAt ℝ (yF X) 0
  swap
  · simp [dY, fderiv_zero_of_not_differentiableAt hd]
  have hY : ∀ k j : Fin r, DifferentiableAt ℝ (fun w => yF X w τ k j) 0 := by
    intro k j
    exact differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hd τ) k) j
  have hN : ∀ k m : Fin r, DifferentiableAt ℝ (fun w : V (nd X) => nmat X w τ k m) 0 := fun k m =>
    ((PoinPf.diff_nmat X τ k m) 0).restrictScalars ℝ
  have hB : ∀ n : ℕ, ∀ k : Fin r, k.val = n → DifferentiableAt ℝ (fun w => gsB X w τ k a) 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hk
      have hrepr : (fun w => gsB X w τ k a) = fun w => yF X w τ k a -
          ∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m a := by
        funext w; rw [yF_expand]; ring
      rw [hrepr]
      refine (hY k a).sub (DifferentiableAt.fun_sum fun m hm => (hN k m).mul (ih m.val ?_ m rfl))
      have := (Finset.mem_filter.1 hm).2
      rw [Fin.lt_def] at this
      omega
  have hN0 : ∀ m : Fin r, m < a → nmat X 0 τ a m = 0 := by
    intro m hm
    have := congrFun (congrFun (PoinPf.nmat_zero X τ) a) m
    simp only [mat, Matrix.of_apply, Matrix.one_apply, hm.ne', if_false] at this
    exact this
  have hB0 : ∀ m : Fin r, m < a → gsB X 0 τ m a = 0 := by
    intro m hm
    rw [gsB_zero, Matrix.one_apply, if_neg hm.ne]
  have hsum : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a)
      (0 : V (nd X) →L[ℝ] ℂ) 0 := by
    have h : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a)
        (∑ m ∈ Finset.univ.filter (· < a), (nmat X 0 τ a m • fderiv ℝ (fun w => gsB X w τ m a) 0 +
          gsB X 0 τ m a • fderiv ℝ (fun w : V (nd X) => nmat X w τ a m) 0)) 0 :=
      HasFDerivAt.fun_sum (fun m _ => (hN a m).hasFDerivAt.mul (hB m.val m rfl).hasFDerivAt)
    convert h using 1
    symm
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' := (Finset.mem_filter.1 hm).2
    rw [hN0 m hm', hB0 m hm', zero_smul, zero_smul, add_zero]
  have him : HasFDerivAt (fun w => (yF X w τ a a).im) (0 : V (nd X) →L[ℝ] ℝ) 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) hsum
    rw [ContinuousLinearMap.comp_zero] at h
    have hf : (fun w => (yF X w τ a a).im) =
        ⇑Complex.imCLM ∘ fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a := by
      funext w
      simp only [Function.comp_apply, Complex.imCLM_apply]
      rw [yF_expand, Complex.add_im, gsB_diag, Complex.ofReal_im, add_zero]
    rw [hf]; exact h
  let L : (X.Ψ → Fin r → Fin r → ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) a).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin r → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X.Ψ => Fin r → Fin r → ℂ) τ))
  have hc : HasFDerivAt (fun w => (yF X w τ a a).im) (Complex.imCLM.comp (L.comp (dY X))) 0 :=
    Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) (L.hasFDerivAt.comp (0 : V (nd X)) hd.hasFDerivAt)
  have := congrArg (fun L => L z) (hc.unique him)
  simpa [L] using this

end GlobalTheory.SUChartSection
