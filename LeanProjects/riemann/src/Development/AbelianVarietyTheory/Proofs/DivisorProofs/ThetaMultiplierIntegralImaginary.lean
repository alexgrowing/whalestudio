import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaLiouville

open Matrix Complex

theorem conj_form {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (w l : Fin g → ℂ) :
    l ⬝ᵥ Hm.mulVec (star w) = (starRingEnd ℂ) (w ⬝ᵥ Hm.mulVec (star l)) := by
  simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : (starRingEnd ℂ) (Hm i j) = Hm j i := by
    have := hH.apply j i
    simpa using this
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_conj]
  rw [h1]
  ring

theorem exists_basis_in {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (s : Set (Fin g → ℂ)) (b : Module.Basis s ℝ (Fin g → ℂ)), Finite s ∧ ∀ i, b i ∈ Λ := by
  obtain ⟨s, hs, hsp, hli⟩ := exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))
  let b := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, hΛ])
  refine ⟨s, b, ?_, ?_⟩
  · exact Module.Finite.finite_basis b
  · intro i
    rw [Module.Basis.mk_apply]
    exact hs i.2

end GlobalTheory.ThetaLiouville

namespace GlobalTheory.ThetaLiouville

open Matrix Complex

theorem im_form_mem_int (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (w : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ)
    (hθ : Differentiable ℂ θ) (hθ0 : ∀ z, θ z ≠ 0)
    (hper : ∀ l ∈ Λ, ∀ z, θ (z + l) = Complex.exp (Real.pi * (w ⬝ᵥ Hm.mulVec (star l))) * θ z) :
    ∀ l ∈ Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n := by
  set u : Fin g → ℂ := Hm.mulVec (star w) with hu
  let ψ : (Fin g → ℂ) → ℂ := fun z => θ z * Complex.exp (-(Real.pi * (z ⬝ᵥ u)))
  have hlin : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ u) := by
    have : (fun z : Fin g → ℂ => z ⬝ᵥ u) = fun z => ∑ i, z i * u i := rfl
    rw [this]
    exact Differentiable.fun_sum fun i _ => (differentiable_apply i).mul_const _
  have hψ : Differentiable ℂ ψ :=
    hθ.mul ((hlin.const_mul _).neg.cexp)

  have hshift : ∀ l ∈ Λ, ∀ z, ψ (z + l) = ψ z *
      Complex.exp (Real.pi * (((2 * (w ⬝ᵥ Hm.mulVec (star l)).im : ℝ) : ℂ) * I)) := by
    intro l hl z
    have hc := conj_form Hm hH w l
    simp only [ψ, hper l hl z, add_dotProduct]
    rw [hc]
    set a := w ⬝ᵥ Hm.mulVec (star l)
    have hsub : a - (starRingEnd ℂ) a = ((2 * a.im : ℝ) : ℂ) * I := by
      rw [Complex.sub_conj]
    rw [← hsub]
    rw [show -(↑Real.pi * (z ⬝ᵥ u + (starRingEnd ℂ) a)) =
        -(↑Real.pi * (z ⬝ᵥ u)) + (-(↑Real.pi * (starRingEnd ℂ) a)) by ring,
      Complex.exp_add,
      show (↑Real.pi * (a - (starRingEnd ℂ) a)) = ↑Real.pi * a + (-(↑Real.pi * (starRingEnd ℂ) a))
        by ring, Complex.exp_add]
    ring
  have hnorm : ∀ l ∈ Λ, ∀ z, ‖ψ (z + l)‖ = ‖ψ z‖ := by
    intro l hl z
    rw [hshift l hl z, norm_mul, Complex.norm_exp]
    simp

  obtain ⟨s, b, hfin, hbΛ⟩ := exists_basis_in Λ hΛ
  haveI : Fintype s := Fintype.ofFinite s
  have hspan : ∀ x ∈ Submodule.span ℤ (Set.range b), x ∈ Λ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hbΛ i
    | zero => exact Λ.zero_mem
    | add x y _ _ hx hy => exact Λ.add_mem hx hy
    | smul n x _ hx => exact Λ.toAddSubgroup.zsmul_mem hx n
  have hcpt : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hψ.continuous.continuousOn
  have hbd : Bornology.IsBounded (Set.range ψ) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hz : z = ZSpan.fract b z + (ZSpan.floor b z : Fin g → ℂ) := by
      rw [ZSpan.fract_apply]; abel
    rw [hz, hnorm _ (hspan _ (ZSpan.floor b z).2)]
    exact hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain b z))
  intro l hl
  have hconst : ψ (0 + l) = ψ 0 := hψ.apply_eq_apply_of_bounded hbd _ _
  rw [hshift l hl 0] at hconst
  have hψ0 : ψ 0 ≠ 0 := mul_ne_zero (hθ0 0) (Complex.exp_ne_zero _)
  have hexp : Complex.exp (Real.pi * (((2 * (w ⬝ᵥ Hm.mulVec (star l)).im : ℝ) : ℂ) * I)) = 1 := by
    have := hconst
    rw [mul_eq_left₀ hψ0] at this
    exact this
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨n, ?_⟩
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : ((w ⬝ᵥ Hm.mulVec (star l)).im : ℂ) = n := by
    have : (Real.pi : ℂ) * 2 * I * ((w ⬝ᵥ Hm.mulVec (star l)).im : ℂ) =
        (Real.pi : ℂ) * 2 * I * n := by
      push_cast at hn
      linear_combination hn
    have h0 : (Real.pi : ℂ) * 2 * I ≠ 0 := mul_ne_zero (mul_ne_zero hpi two_ne_zero) hI
    exact mul_left_cancel₀ h0 this
  exact_mod_cast h2

end GlobalTheory.ThetaLiouville
