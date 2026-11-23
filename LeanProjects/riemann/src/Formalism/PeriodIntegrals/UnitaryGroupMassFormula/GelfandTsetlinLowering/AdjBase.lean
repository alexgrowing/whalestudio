import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitPowerNormScale.NormUnitsZpowSq

noncomputable section

namespace PI.WGL.Adj

open Formalism.BasicNotions MvPolynomial

theorem fockF_eq_sum_of_subset {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS ?_
  intro m _ hm
  simp only [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fockF_add_left {σ : Type} [DecidableEq σ] (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  rw [fockF_eq_sum_of_subset (f + f') g _ MvPolynomial.support_add,
    fockF_eq_sum_of_subset f g _ Finset.subset_union_left,
    fockF_eq_sum_of_subset f' g _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem fockF_add_right {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (g + g') = Formalism.REAL.fockF f g + Formalism.REAL.fockF f g' := by
  unfold Formalism.REAL.fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]; ring

theorem den_pos {N : ℕ} (lam : DomWeight N) :
    0 < (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re ∧
      (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).im = 0 :=
  Formalism.GradedWeylDivisibility.fockPos _ _ (Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW)

theorem den_eq {N : ℕ} (lam : DomWeight N) :
    Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam) =
      (((Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [(den_pos lam).2])

theorem nf_eq {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f g = Formalism.REAL.fockF f g /
      (((Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re : ℝ) : ℂ) := by
  unfold normFock; rw [← den_eq]

theorem nf_herm {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam g f = star (normFock lam f g) := by
  rw [nf_eq, nf_eq, Formalism.GradedWeylDivisibility.fockHerm, star_div₀, Complex.star_def, Complex.conj_ofReal]

theorem nf_add_left {N : ℕ} (lam : DomWeight N) (f f' g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (f + f') g = normFock lam f g + normFock lam f' g := by
  unfold normFock; rw [fockF_add_left, add_div]

theorem nf_add_right {N : ℕ} (lam : DomWeight N) (f g g' : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (g + g') = normFock lam f g + normFock lam f g' := by
  unfold normFock; rw [fockF_add_right, add_div]

theorem nf_smul_left {N : ℕ} (lam : DomWeight N) (c : ℂ) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (c • f) g = c * normFock lam f g := by
  unfold normFock; rw [PI.WHw.bC_smul_left, mul_div_assoc]

theorem nf_smul_right {N : ℕ} (lam : DomWeight N) (c : ℂ) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (c • g) = star c * normFock lam f g := by
  unfold normFock; rw [PI.WHw.bC_smul_right, mul_div_assoc]

def nfL {N : ℕ} (lam : DomWeight N) (g : MvPolynomial (Fin N × Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ where
  toFun f := normFock lam f g
  map_add' f f' := nf_add_left lam f f' g
  map_smul' c f := by simp [nf_smul_left]

theorem nfL_apply {N : ℕ} (lam : DomWeight N) (g f : MvPolynomial (Fin N × Fin N) ℂ) :
    nfL lam g f = normFock lam f g := rfl

theorem nf_sum_smul_left {N : ℕ} (lam : DomWeight N) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (v : ι → MvPolynomial (Fin N × Fin N) ℂ) (g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (∑ k ∈ S, a k • v k) g = ∑ k ∈ S, a k * normFock lam (v k) g := by
  rw [← nfL_apply, map_sum]
  simp [nfL_apply]

theorem nf_sum_smul_right {N : ℕ} (lam : DomWeight N) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (v : ι → MvPolynomial (Fin N × Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (∑ k ∈ S, a k • v k) = ∑ k ∈ S, star (a k) * normFock lam f (v k) := by
  rw [nf_herm, nf_sum_smul_left, star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul', ← nf_herm]

theorem nf_sub_right {N : ℕ} (lam : DomWeight N) (f g g' : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (g - g') = normFock lam f g - normFock lam f g' := by
  rw [nf_herm, ← nfL_apply, map_sub, star_sub, nfL_apply, nfL_apply, ← nf_herm, ← nf_herm]

theorem nf_zero_right {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f 0 = 0 := by
  have := nf_smul_right lam 0 f 0
  simpa using this

theorem nf_self_im {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    (normFock lam f f).im = 0 := by
  rw [nf_eq, Complex.div_ofReal_im]
  by_cases hf : f = 0
  · subst hf; simp [Formalism.REAL.fockF]
  · rw [(Formalism.GradedWeylDivisibility.fockPos _ f hf).2, zero_div]

theorem nf_self_re_pos {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ≠ 0) :
    0 < (normFock lam f f).re := by
  rw [nf_eq, Complex.div_ofReal_re]
  exact div_pos (Formalism.GradedWeylDivisibility.fockPos _ f hf).1 (den_pos lam).1

theorem nf_self_re_nonneg {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    0 ≤ (normFock lam f f).re := by
  by_cases hf : f = 0
  · subst hf; rw [nf_zero_right]; simp
  · exact (nf_self_re_pos lam f hf).le

theorem nf_self_eq_zero {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (h : normFock lam f f = 0) : f = 0 := by
  by_contra hf
  have := nf_self_re_pos lam f hf
  rw [h] at this; simp at this

theorem nf_self_eq_re {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f f = (((normFock lam f f).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [nf_self_im])

theorem nf_extremal {N : ℕ} (lam : DomWeight N) :
    normFock lam (extremal ℂ N lam) (extremal ℂ N lam) = 1 := by
  unfold normFock
  refine div_self ?_
  intro h0
  have := (den_pos lam).1
  rw [h0] at this; simp at this

def nfCore {N : ℕ} (lam : DomWeight N) : InnerProductSpace.Core ℂ (MvPolynomial (Fin N × Fin N) ℂ) where
  inner x y := normFock lam y x
  conj_inner_symm x y := by
    show starRingEnd ℂ (normFock lam x y) = normFock lam y x
    rw [starRingEnd_apply, ← nf_herm]
  re_inner_nonneg x := nf_self_re_nonneg lam x
  add_left x y z := nf_add_right lam z x y
  smul_left x y r := by
    show normFock lam y (r • x) = starRingEnd ℂ r * normFock lam y x
    rw [nf_smul_right, starRingEnd_apply]
  definite x hx := nf_self_eq_zero lam x hx

theorem nf_cauchy_schwarz {N : ℕ} (lam : DomWeight N) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    ‖normFock lam y x‖ * ‖normFock lam x y‖ ≤ (normFock lam x x).re * (normFock lam y y).re := by
  letI : PreInnerProductSpace.Core ℂ (MvPolynomial (Fin N × Fin N) ℂ) := (nfCore lam).toCore
  exact InnerProductSpace.Core.inner_mul_inner_self_le x y

def frameCore (n : ℕ) (sg : DomWeight n) : InnerProductSpace.Core ℂ (nablaSq ℂ n sg) where
  inner x y := normFock sg (y : MvPolynomial (Fin n × Fin n) ℂ) x
  conj_inner_symm x y := by
    show starRingEnd ℂ (normFock sg (x : MvPolynomial (Fin n × Fin n) ℂ) y) = normFock sg (y : MvPolynomial (Fin n × Fin n) ℂ) x
    rw [starRingEnd_apply, ← nf_herm]
  re_inner_nonneg x := nf_self_re_nonneg sg x
  add_left x y z := by
    show normFock sg (z : MvPolynomial (Fin n × Fin n) ℂ) ((x + y : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ) = _
    rw [Submodule.coe_add, nf_add_right]
  smul_left x y r := by
    show normFock sg (y : MvPolynomial (Fin n × Fin n) ℂ) ((r • x : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ) = _
    rw [Submodule.coe_smul, nf_smul_right, starRingEnd_apply]
  definite x hx := by
    have := nf_self_eq_zero sg (x : MvPolynomial (Fin n × Fin n) ℂ) hx
    exact Subtype.ext this

theorem exists_frame (n : ℕ) (sg : DomWeight n) :
    ∃ (d : ℕ) (b : Fin d → MvPolynomial (Fin n × Fin n) ℂ), (∀ k, b k ∈ nablaSq ℂ n sg) ∧
      ∀ s ∈ nablaSq ℂ n sg, s = ∑ k, normFock sg s (b k) • b k := by
  letI : NormedAddCommGroup (nablaSq ℂ n sg) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (frameCore n sg)
  letI : InnerProductSpace ℂ (nablaSq ℂ n sg) := InnerProductSpace.ofCore (frameCore n sg).toCore
  haveI : FiniteDimensional ℂ (nablaSq ℂ n sg) := PI.WHw.bC_fd n n sg.natW
  let b := stdOrthonormalBasis ℂ (nablaSq ℂ n sg)
  refine ⟨Module.finrank ℂ (nablaSq ℂ n sg), fun k => (b k : MvPolynomial (Fin n × Fin n) ℂ),
    fun k => (b k).2, fun s hs => ?_⟩
  have h1 := congrArg Subtype.val (b.sum_repr' ⟨s, hs⟩)
  rw [Submodule.coe_sum] at h1
  exact h1.symm

end PI.WGL.Adj
