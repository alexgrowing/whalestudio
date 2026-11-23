import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingLinkFamilyNormalised
import Formalism.LocalToGlobal.GlobalTheory.GL4.InitMinorIdEqLpMinor
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)

theorem fock_eq_sum_coeff {σ : Type} (f g : MvPolynomial σ ℂ) (t : Finset (σ →₀ ℕ)) (ht : f.support ⊆ t) :
    fockF f g = ∑ m ∈ t, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset ht
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [h0, zero_mul, zero_mul]

theorem fockF_add_left_g_l4 {σ : Type} (f f' g : MvPolynomial σ ℂ) :
    fockF (f + f') g = fockF f g + fockF f' g := by
  classical
  rw [fock_eq_sum_coeff (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    fock_eq_sum_coeff f g (f.support ∪ f'.support) Finset.subset_union_left,
    fock_eq_sum_coeff f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fock_conj_symm {σ : Type} (f g : MvPolynomial σ ℂ) : fockF g f = star (fockF f g) := by
  classical
  rw [fock_eq_sum_coeff g f (f.support ∪ g.support) Finset.subset_union_right,
    fock_eq_sum_coeff f g (f.support ∪ g.support) Finset.subset_union_left, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [star_mul', star_mul', star_star, star_natCast]
  ring

theorem fockF_add_right_g_l4 {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    fockF f (g + g') = fockF f g + fockF f g' := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring

theorem fockF_smul_left' {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (c • f) g = c * fockF f g := by
  rw [fock_eq_sum_coeff (c • f) g f.support MvPolynomial.support_smul]
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fockF_smul_right_eq_star_mul {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (c • g) = star c * fockF f g := by
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem fock_self_re_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ (fockF f f).re := by
  by_cases hf : f = 0
  · subst hf
    unfold fockF
    simp
  · exact (Formalism.GradedWeylDivisibility.fockPos σ f hf).1.le

theorem fock_self_im_eq_zero {σ : Type} (f : MvPolynomial σ ℂ) : (fockF f f).im = 0 := by
  by_cases hf : f = 0
  · subst hf
    unfold fockF
    simp
  · exact (Formalism.GradedWeylDivisibility.fockPos σ f hf).2

theorem fock_self_eq_re {σ : Type} (f : MvPolynomial σ ℂ) : fockF f f = (((fockF f f).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simp [fock_self_im_eq_zero f]

def fockLin {σ : Type} (G : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun F := fockF F G
  map_add' F F' := fockF_add_left_g_l4 F F' G
  map_smul' c F := by rw [fockF_smul_left', smul_eq_mul, RingHom.id_apply]

theorem fockLin_apply {σ : Type} (G F : MvPolynomial σ ℂ) : fockLin G F = fockF F G := rfl

def FockSp (σ : Type) : Type := MvPolynomial σ ℂ

instance (σ : Type) : AddCommGroup (FockSp σ) := inferInstanceAs (AddCommGroup (MvPolynomial σ ℂ))
instance (σ : Type) : Module ℂ (FockSp σ) := inferInstanceAs (Module ℂ (MvPolynomial σ ℂ))

instance fockCore (σ : Type) : InnerProductSpace.Core ℂ (FockSp σ) where
  inner f g := fockF (show MvPolynomial σ ℂ from g) (show MvPolynomial σ ℂ from f)
  conj_inner_symm x y := by
    show (starRingEnd ℂ) (fockF (show MvPolynomial σ ℂ from x) (show MvPolynomial σ ℂ from y)) =
      fockF (show MvPolynomial σ ℂ from y) (show MvPolynomial σ ℂ from x)
    rw [starRingEnd_apply, ← fock_conj_symm]
  re_inner_nonneg x := fock_self_re_nonneg (show MvPolynomial σ ℂ from x)
  add_left x y z := fockF_add_right_g_l4 (show MvPolynomial σ ℂ from z) (show MvPolynomial σ ℂ from x)
    (show MvPolynomial σ ℂ from y)
  smul_left x y r := by
    show fockF (show MvPolynomial σ ℂ from y) (r • (show MvPolynomial σ ℂ from x)) = _
    rw [fockF_smul_right_eq_star_mul, starRingEnd_apply]
  definite x hx := by
    by_contra hne
    have h := (Formalism.GradedWeylDivisibility.fockPos σ (show MvPolynomial σ ℂ from x) hne).1
    have h0 : fockF (show MvPolynomial σ ℂ from x) (show MvPolynomial σ ℂ from x) = 0 := hx
    rw [h0, Complex.zero_re] at h
    exact lt_irrefl _ h

instance (σ : Type) : NormedAddCommGroup (FockSp σ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (FockSp σ) _ _ _ (fockCore σ)

instance (σ : Type) : InnerProductSpace ℂ (FockSp σ) := InnerProductSpace.ofCore (fockCore σ).toCore

theorem fockSp_inner {σ : Type} (f g : FockSp σ) :
    (inner ℂ f g : ℂ) = fockF (show MvPolynomial σ ℂ from g) (show MvPolynomial σ ℂ from f) := rfl

theorem fock_cauchy_schwarz {σ : Type} (f g : MvPolynomial σ ℂ) : ‖fockF f g‖ ^ 2 ≤ (fockF f f).re * (fockF g g).re := by
  have h := inner_mul_inner_self_le (𝕜 := ℂ) (show FockSp σ from f) (show FockSp σ from g)
  have h' : ‖fockF g f‖ * ‖fockF f g‖ ≤ (fockF f f).re * (fockF g g).re := h
  rw [fock_conj_symm f g, norm_star] at h'
  rw [sq]
  exact h'

theorem fock_adjoint_bound {κ ι : Type} (p : MvPolynomial κ ℂ) (Y J : MvPolynomial ι ℂ) (K : ℝ) (hK : 0 ≤ K)
    (h1 : fockF p p = fockF Y J) (h2 : (fockF J J).re ≤ K * (fockF p p).re) :
    (fockF p p).re ≤ K * (fockF Y Y).re := by
  have hP : 0 ≤ (fockF p p).re := fock_self_re_nonneg p
  have hYn : 0 ≤ (fockF Y Y).re := fock_self_re_nonneg Y
  have hJn : 0 ≤ (fockF J J).re := fock_self_re_nonneg J
  have hcs := fock_cauchy_schwarz Y J
  have hre : (fockF p p).re ≤ ‖fockF Y J‖ := by
    rw [h1]
    exact RCLike.re_le_norm (fockF Y J)
  nlinarith [mul_le_mul_of_nonneg_left h2 hYn, mul_self_le_mul_self hP hre, mul_nonneg hK hYn]

theorem fockF_finset_sum_left {σ ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ ℂ) (g : MvPolynomial σ ℂ) :
    fockF (∑ i ∈ s, f i) g = ∑ i ∈ s, fockF (f i) g := by
  exact map_sum (fockLin g) f s

theorem fockF_finset_sum_right {σ ι : Type} (s : Finset ι) (f : MvPolynomial σ ℂ) (g : ι → MvPolynomial σ ℂ) :
    fockF f (∑ i ∈ s, g i) = ∑ i ∈ s, fockF f (g i) := by
  rw [fock_conj_symm (∑ i ∈ s, g i) f, fockF_finset_sum_left, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (fock_conj_symm (g i) f).symm

theorem fock_adjoint_exists {κ ι : Type} (V : Submodule ℂ (MvPolynomial κ ℂ)) [FiniteDimensional ℂ V]
    (j : V →ₗ[ℂ] MvPolynomial ι ℂ) :
    ∃ P : MvPolynomial ι ℂ →ₗ[ℂ] MvPolynomial κ ℂ,
      (∀ F, P F ∈ V) ∧ ∀ F (v : V), fockF (P F) (v : MvPolynomial κ ℂ) = fockF F (j v) := by
  classical
  let V' : Submodule ℂ (FockSp κ) := V
  haveI : FiniteDimensional ℂ V' := ‹FiniteDimensional ℂ V›
  let e := stdOrthonormalBasis ℂ V'
  let ev : Fin (Module.finrank ℂ V') → V := fun k => ⟨((e k : V') : FockSp κ), (e k).2⟩
  refine ⟨∑ k, (fockLin (j (ev k))).smulRight ((ev k : V) : MvPolynomial κ ℂ), ?_, ?_⟩
  · intro F
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (ev k).2
  · intro F v
    let v' : V' := ⟨v.1, v.2⟩
    have hv : v = ∑ l, (inner ℂ (e l) v') • ev l := by
      apply Subtype.ext
      have h2 := congrArg (fun x : V' => (x : FockSp κ)) (e.sum_repr' v')
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2 ⊢
      exact h2.symm
    conv_rhs => rw [hv]
    rw [map_sum, fockF_finset_sum_right]
    simp only [map_smul, fockF_smul_right_eq_star_mul, LinearMap.sum_apply, LinearMap.smulRight_apply,
      fockF_finset_sum_left, fockF_smul_left', fockLin_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
    congr 1
    exact fock_conj_symm (v : MvPolynomial κ ℂ) ((ev l : V) : MvPolynomial κ ℂ)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
