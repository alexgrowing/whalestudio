import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace MCGramEntryDeriv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem comp_linearIsometry {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : F' →ₗᵢ[ℝ] ℂ) (φ : F' → ℂ) (hφ : ∀ x, L x = φ x) {f : E → F'} {p : E}
    (hf : DifferentiableAt ℝ f p) :
    DifferentiableAt ℝ (fun q => φ (f q)) p ∧
      ‖fderiv ℝ (fun q => φ (f q)) p‖ = ‖fderiv ℝ f p‖ := by
  have hfun : (fun q => φ (f q)) = fun q => L (f q) := funext fun q => (hφ _).symm
  have hL : HasFDerivAt (fun q => L (f q)) (L.toContinuousLinearMap.comp (fderiv ℝ f p)) p :=
    L.toContinuousLinearMap.hasFDerivAt.comp p hf.hasFDerivAt
  rw [hfun]
  exact ⟨hL.differentiableAt, by rw [hL.fderiv, L.norm_toContinuousLinearMap_comp]⟩

theorem triple {u v w : E → ℂ} {p : E} (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) (hw : DifferentiableAt ℝ w p) :
    DifferentiableAt ℝ (fun q => u q * v q * w q) p ∧
      ‖fderiv ℝ (fun q => u q * v q * w q) p‖ ≤
        ‖fderiv ℝ u p‖ * ‖v p‖ * ‖w p‖ + ‖u p‖ * ‖fderiv ℝ v p‖ * ‖w p‖ +
          ‖u p‖ * ‖v p‖ * ‖fderiv ℝ w p‖ := by
  have huv : DifferentiableAt ℝ (fun q => u q * v q) p := hu.mul hv
  refine ⟨huv.mul hw, ?_⟩
  rw [fderiv_fun_mul huv hw, fderiv_fun_mul hu hv]
  have h1 := norm_add_le ((u p * v p) • fderiv ℝ w p)
    (w p • (u p • fderiv ℝ v p + v p • fderiv ℝ u p))
  have h2 := norm_add_le (u p • fderiv ℝ v p) (v p • fderiv ℝ u p)
  rw [norm_smul, norm_smul, norm_mul] at h1
  rw [norm_smul, norm_smul] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (w p))
  nlinarith

theorem mul_three_le_mul_three {x y z X Y W : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hx : x ≤ X)
    (hy : y ≤ Y) (hz : z ≤ W) : x * y * z ≤ X * Y * W :=
  mul_le_mul (mul_le_mul hx hy hy0 (hx0.trans hx)) hz hz0
    (mul_nonneg (hx0.trans hx) (hy0.trans hy))

end MCGramEntryDeriv

open MCGramEntryDeriv in

theorem GramEntryDeriv.proof : GramEntryDeriv.Statement := by
  intro E _ _ g k F Z p a e e' hF hZ j l
  have hent : ∀ q, ((F q)ᴴ * (Z q).map (fun x : ℝ => (x : ℂ)) * F q) j l =
      ∑ t, ∑ s, star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l := by
    intro q
    simp [Matrix.mul_apply, Finset.sum_mul]
  have hfun : (fun q => ((F q)ᴴ * (Z q).map (fun x : ℝ => (x : ℂ)) * F q) j l) =
      fun q => ∑ t, ∑ s, star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l := funext hent
  rw [hfun, hent p]
  have hterm : ∀ t s : Fin g,
      DifferentiableAt ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p ∧
      ‖star (F p s j) * ((Z p s t : ℝ) : ℂ) * F p t l‖ ≤ a ^ 2 * e ∧
      ‖fderiv ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p‖ ≤
        2 * a ^ 2 * e + a ^ 2 * e' := by
    intro t s
    obtain ⟨hd1, hn1, hD1⟩ := hF s j
    obtain ⟨hd3, hn3, hD3⟩ := hF t l
    obtain ⟨hd2, hn2, hD2⟩ := hZ s t
    obtain ⟨hu, hu'⟩ := comp_linearIsometry Complex.conjLIE.toLinearIsometry
      (fun z : ℂ => star z) (fun z => rfl) hd1
    obtain ⟨hv, hv'⟩ := comp_linearIsometry Complex.ofRealLI
      (fun x : ℝ => (x : ℂ)) (fun x => rfl) hd2
    obtain ⟨hdiff, hbound⟩ := triple hu hv hd3
    have hnu : ‖star (F p s j)‖ ≤ a := by rw [norm_star]; exact hn1
    have hnv : ‖((Z p s t : ℝ) : ℂ)‖ ≤ e := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hn2
    have hDu : ‖fderiv ℝ (fun q => star (F q s j)) p‖ ≤ a := hu'.le.trans hD1
    have hDv : ‖fderiv ℝ (fun q => ((Z q s t : ℝ) : ℂ)) p‖ ≤ e' := hv'.le.trans hD2
    refine ⟨hdiff, ?_, ?_⟩
    · rw [norm_mul, norm_mul]
      calc ‖star (F p s j)‖ * ‖((Z p s t : ℝ) : ℂ)‖ * ‖F p t l‖ ≤ a * e * a :=
            mul_three_le_mul_three (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hnu hnv hn3
        _ = a ^ 2 * e := by ring
    · refine hbound.trans ?_
      have b1 := mul_three_le_mul_three (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hDu hnv hn3
      have b2 := mul_three_le_mul_three (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hnu hDv hn3
      have b3 := mul_three_le_mul_three (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hnu hnv hD3
      nlinarith
  have hH : HasFDerivAt (fun q => ∑ t, ∑ s, star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l)
      (∑ t, ∑ s, fderiv ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p) p :=
    HasFDerivAt.fun_sum fun t _ => HasFDerivAt.fun_sum fun s _ => (hterm t s).1.hasFDerivAt
  refine ⟨hH.differentiableAt, ?_, ?_⟩
  · calc ‖∑ t, ∑ s, star (F p s j) * ((Z p s t : ℝ) : ℂ) * F p t l‖
          ≤ ∑ t : Fin g, ∑ s : Fin g, ‖star (F p s j) * ((Z p s t : ℝ) : ℂ) * F p t l‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => norm_sum_le _ _)
      _ ≤ ∑ t : Fin g, ∑ s : Fin g, a ^ 2 * e :=
            Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun s _ => (hterm t s).2.1
      _ = (g : ℝ) ^ 2 * a ^ 2 * e := by simp [Finset.sum_const]; ring
  · rw [hH.fderiv]
    calc ‖∑ t, ∑ s, fderiv ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p‖
          ≤ ∑ t : Fin g, ∑ s : Fin g,
              ‖fderiv ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => norm_sum_le _ _)
      _ ≤ ∑ t : Fin g, ∑ s : Fin g, (2 * a ^ 2 * e + a ^ 2 * e') :=
            Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun s _ => (hterm t s).2.2
      _ = (g : ℝ) ^ 2 * (2 * a ^ 2 * e + a ^ 2 * e') := by simp [Finset.sum_const]; ring

end GroundTheory.Heights₂.Heights
