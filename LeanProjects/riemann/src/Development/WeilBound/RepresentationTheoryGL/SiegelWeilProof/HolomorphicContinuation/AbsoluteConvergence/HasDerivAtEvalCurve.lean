import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousEvX

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def scal (α : Fin n → ℝ) (x : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ := fun a j => (α j : ℂ) * x a j

def aH (X : Fin n → ℝ) (h : ℝ) : Fin n → ℝ := fun j => Real.exp (h * X j)

theorem ept_scal (α : Fin n → ℝ) (x : Fin m → Fin n → ℂ) :
    ept (scal α x) = fun k => (α k.2.1 : ℂ) * ept x k := by
  funext k
  unfold ept scal
  split_ifs
  · simp [star_mul', Complex.conj_ofReal]
  · rfl

theorem hasDerivAt_eval_curve {σ : Type*} [Fintype σ] [DecidableEq σ] (Q : MvPolynomial σ ℂ) (w : ℝ → σ → ℂ)
    (w' : σ → ℂ) (h : ℝ) (hw : ∀ k, HasDerivAt (fun s => w s k) (w' k) h) :
    HasDerivAt (fun s => eval (w s) Q) (∑ k, eval (w h) (pderiv k Q) * w' k) h := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const h a
  | add p q hp hq =>
    have e : (∑ k, eval (w h) (pderiv k (p + q)) * w' k) =
        (∑ k, eval (w h) (pderiv k p) * w' k) + ∑ k, eval (w h) (pderiv k q) * w' k := by
      simp [map_add, add_mul, Finset.sum_add_distrib]
    rw [e]
    exact (hp.add hq).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp)
  | mul_X p i hp =>
    have e : ∑ k, eval (w h) (pderiv k (p * X i)) * w' k =
        (∑ k, eval (w h) (pderiv k p) * w' k) * w h i + eval (w h) p * w' i := by
      have e1 : ∀ k, eval (w h) (pderiv k (p * X i)) * w' k =
          eval (w h) (pderiv k p) * w' k * w h i + (if k = i then eval (w h) p * w' i else 0) := by
        intro k
        rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, eval_X]
        by_cases hk : k = i
        · subst hk; simp; ring
        · simp [Pi.single_apply, hk]; ring
      simp only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
    rw [e]
    exact (hp.mul (hw i)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp)

theorem hasDerivAt_scal_coord (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) (h : ℝ) (k : Fin m × Fin n × Bool) :
    HasDerivAt (fun s => ept (scal (aH X s) y) k) ((X k.2.1 : ℂ) * ept (scal (aH X h) y) k) h := by
  simp only [ept_scal, aH]
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (s * X k.2.1)) (Real.exp (h * X k.2.1) * X k.2.1) h := by
    simpa using ((hasDerivAt_id h).mul_const (X k.2.1)).exp
  have h2 := (h1.ofReal_comp).mul_const (ept y k)
  refine h2.congr_deriv ?_
  rw [Complex.ofReal_mul]; ring

theorem integral_scal (α : Fin n → ℝ) (hα : ∀ j, 0 < α j) (f : (Fin m → Fin n → ℂ) → ℂ) :
    ∫ x, f x = (∏ j, α j ^ (2 * m) : ℝ) * ∫ y, f (scal α y) := by
  let Li : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := LinearMap.pi fun j => (α j • LinearMap.id).comp (LinearMap.proj j)
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a => Li.comp (LinearMap.proj a)
  have hL : ∀ y, L y = scal α y := by
    intro y; funext a j; simp [L, Li, scal, Complex.real_smul]
  have hdetLi : LinearMap.det Li = ∏ j, α j ^ 2 := by
    simp only [Li, LinearMap.det_pi, LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, mul_one]
  have hdet : LinearMap.det L = ∏ j, α j ^ (2 * m) := by
    simp only [L, LinearMap.det_pi, hdetLi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have hD : 0 < ∏ j, α j ^ (2 * m) := Finset.prod_pos fun j _ => pow_pos (hα j) _
  let Linv : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a =>
    (LinearMap.pi fun j => ((α j)⁻¹ • LinearMap.id).comp (LinearMap.proj j)).comp (LinearMap.proj a)
  let Le : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearEquiv.ofLinear L Linv
    (LinearMap.ext fun y => funext fun a => funext fun j => by
      have h0 : (α j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα j).ne'
      simp only [L, Li, Linv, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.id_coe, id_eq, Complex.real_smul, Complex.ofReal_inv]
      field_simp)
    (LinearMap.ext fun y => funext fun a => funext fun j => by
      have h0 : (α j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα j).ne'
      simp only [L, Li, Linv, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.id_coe, id_eq, Complex.real_smul, Complex.ofReal_inv]
      field_simp)
  have hH1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := by infer_instance
  have hH2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := Le.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = scal α y := fun y => hL y
  have hmap : Measure.map e (volume : Measure (Fin m → Fin n → ℂ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume := by
    have : (e : (Fin m → Fin n → ℂ) → (Fin m → Fin n → ℂ)) = L := by funext y; rfl
    rw [this]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact hD.ne')
  have h1 : ∫ y, f (scal α y) = (∏ j, α j ^ (2 * m))⁻¹ * ∫ x, f x := by
    have := integral_map_equiv e f (μ := volume)
    simp only [he] at this
    rw [← this, hmap, integral_smul_measure, hdet, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos (inv_pos.2 hD)]
    simp [Complex.real_smul]
  rw [h1, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hD.ne'), one_mul]

end PositivityTheory.Rg.Sw.AbsSt.DF
