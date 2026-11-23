import Development.EtaleCohomology.EtaleTrace.GenOutChartPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem homog_div_mem {k : Type} [Field k] {K : Type} [Field K] (κ : k →+* K) {N : ℕ} (w : Fin (N + 1) → K)
    (i : Fin (N + 1)) (_hi : w i ≠ 0) (R : Subring K) (hκ : ∀ c, κ c ∈ R) (hw : ∀ j, w j / w i ∈ R)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g.IsHomogeneous m) : eval₂ κ w g / w i ^ m ∈ R := by
  rw [eval₂_eq, Finset.sum_div]
  refine Subring.sum_mem _ fun d hd => ?_
  have hdeg : ∑ j, d j = m := by
    rw [← hg (mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have : (κ (coeff d g) * ∏ j, w j ^ d j) / w i ^ m = κ (coeff d g) * ∏ j, (w j / w i) ^ d j := by
    rw [mul_div_assoc]; congr 1
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  have hsupp : ∏ j ∈ d.support, w j ^ d j = ∏ j, w j ^ d j :=
    Finset.prod_subset (Finset.subset_univ _) (fun j _ hj => by simp [Finsupp.notMem_support_iff.mp hj])
  rw [hsupp, this]
  exact Subring.mul_mem _ (hκ _) (Subring.prod_mem _ fun j _ => Subring.pow_mem _ (hw j) _)

def chartVal {k : Type} [Field k] {K : Type} [Field K] (κ : k →+* K) {N : ℕ} (w : Fin (N + 1) → K) (i : Fin (N + 1))
    (hi : w i ≠ 0) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* K :=
  (IsLocalization.Away.lift (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) (g := eval₂Hom κ w)
    (by simpa using hi.isUnit)).comp
    (algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)))

theorem chartVal_mk {k : Type} [Field k] {K : Type} [Field K] (κ : k →+* K) {N : ℕ} (w : Fin (N + 1) → K)
    (i : Fin (N + 1)) (hi : w i ≠ 0)
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)) :
    chartVal κ w i hi (HomogeneousLocalization.Away.mk _ hx m g hg) = eval₂ κ w g / w i ^ m := by
  simp only [chartVal, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp only [coe_eval₂Hom, eval₂_pow, eval₂_X]
  rw [mul_div_cancel₀ _ (pow_ne_zero _ hi)]

def SectOfLoc : Prop := ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (R : Subring X.functionField),
  (∀ z ∈ R, ∀ y ∈ U, z ∈ loc X y) →
  ∃ φ : R →+* Γ(X, U), ∀ (z : R) (y : X) (hy : y ∈ U),
    algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy (φ z)) = z

theorem ChartRing_of (h : SectOfLoc) : ChartRing := by
  intro k _ X _ p N w i hi U hU hx
  let ψ := chartVal (kHom p) w i hi
  have hR : ∀ z ∈ ψ.range, ∀ y ∈ U, z ∈ loc X y := by
    rintro _ ⟨a, rfl⟩ y hy
    obtain ⟨m, g, hg, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hx a
    rw [chartVal_mk]
    have hg' : g.IsHomogeneous m := by
      simpa using (mem_homogeneousSubmodule _ _).1 hg
    exact homog_div_mem (kHom p) w i hi (loc X y) (fun c => kHom_mem_loc p y c) (fun j => hU y hy j) m g hg'
  obtain ⟨φ, hφ⟩ := h X U ψ.range hR
  refine ⟨φ.comp ψ.rangeRestrict, fun y hy m g hg => ?_⟩
  rw [RingHom.comp_apply, hφ]
  exact chartVal_mk (kHom p) w i hi hx m g hg

theorem GenOutChart_of_sect (h1 : SectOfLoc) (h2 : ChartGen) : GenOutChart :=
  GenOutChart_of (ChartRing_of h1) h2

end LateralTheory.EtaleTrace.Cov
