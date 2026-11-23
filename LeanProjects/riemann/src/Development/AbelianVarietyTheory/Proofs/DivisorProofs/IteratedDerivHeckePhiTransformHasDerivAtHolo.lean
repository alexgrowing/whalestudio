import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTransABTwoZero
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

theorem iteratedDeriv_hTrans_eq_sum
    (h1 : ∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y)
    (n : ℝ) (k : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ → ℂ) (ab : ι → ℕ × ℕ),
      (∀ i, Differentiable ℂ (c i)) ∧ (∀ i, 2 ≤ (ab i).1 + (ab i).2) ∧
      ∀ σ ∈ halfPlane, ∀ y : ℝ, y ≠ 0 →
        iteratedDeriv k (hTrans σ n) y = ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y := by
  induction k with
  | zero =>
    refine ⟨Unit, inferInstance, fun _ _ => 1, fun _ => (2, 0), fun _ => by fun_prop,
      fun _ => by simp, fun σ _ y _ => ?_⟩
    simp [hTransAB_two_zero]
  | succ k ih =>
    obtain ⟨ι, _, c, ab, hc, hab, h⟩ := ih
    refine ⟨ι ⊕ ι, inferInstance,
      Sum.elim (fun i σ => c i σ * (I * (-((ab i).1 : ℂ) - σ)))
        (fun i σ => c i σ * (I * (((ab i).2 : ℂ) + σ))),
      Sum.elim (fun i => ((ab i).1 + 1, (ab i).2)) (fun i => ((ab i).1, (ab i).2 + 1)),
      ?_, ?_, ?_⟩
    · rintro (i | i)
      · have := hc i
        simp only [Sum.elim_inl]; fun_prop
      · have := hc i
        simp only [Sum.elim_inr]; fun_prop
    · rintro (i | i)
      · have := hab i
        simp only [Sum.elim_inl]; omega
      · have := hab i
        simp only [Sum.elim_inr]; omega
    · intro σ hσ y hy
      have hev : iteratedDeriv k (hTrans σ n) =ᶠ[nhds y]
          fun y' => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y' := by
        filter_upwards [isOpen_ne.mem_nhds hy] with y' hy' using h σ hσ y' hy'
      have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
        (h1 (ab i).1 (ab i).2 σ n y (hab i) hσ hy).const_mul (c i σ))).congr_of_eventuallyEq hev
      rw [iteratedDeriv_succ, hd.deriv, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Sum.elim_inl, Sum.elim_inr]
      ring

theorem iteratedDeriv_hTrans_jet :
    (∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y) → (∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane) →
  (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) := by
  intro h1 h2 n k y hy
  obtain ⟨ι, _, c, ab, hc, hab, h⟩ := iteratedDeriv_hTrans_eq_sum h1 n k
  refine ⟨fun σ hσ => ?_, ?_⟩
  · have hev : iteratedDeriv k (hTrans σ n) =ᶠ[nhds y]
        fun y' => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y' := by
      filter_upwards [isOpen_ne.mem_nhds hy] with y' hy' using h σ hσ y' hy'
    have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (h1 (ab i).1 (ab i).2 σ n y (hab i) hσ hy).const_mul (c i σ))).congr_of_eventuallyEq hev
    rw [iteratedDeriv_succ]
    exact hd.differentiableAt.hasDerivAt
  · refine DifferentiableOn.congr
      (f := fun σ => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y) ?_ (fun σ hσ => h σ hσ y hy)
    exact DifferentiableOn.fun_sum fun i _ =>
      (hc i).differentiableOn.mul (h2 _ _ n y (hab i) hy)

end GlobalTheory.HeckeTwo
