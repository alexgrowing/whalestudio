import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic MvPolynomial ReciprocityTheory.MultiplicativeHeights

namespace GlobalTheory.HeightUnique

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.linSubst_linSubst {R : Type} [CommRing R] {B N n m : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (P : Matrix (Fin n) (Fin m) R) (f : MvPolynomial (Fin B × Fin N) R) :
    _root_.GlobalTheory.ChowHt.linSubst P (_root_.GlobalTheory.ChowHt.linSubst M f) = _root_.GlobalTheory.ChowHt.linSubst (M * P) f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  rw [← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro p
  simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.linSubst_one {R : Type} [CommRing R] {B N : ℕ} (f : MvPolynomial (Fin B × Fin N) R) :
    _root_.GlobalTheory.ChowHt.linSubst (1 : Matrix (Fin N) (Fin N) R) f = f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  have hX : (fun p : Fin B × Fin N => ∑ k, C ((1 : Matrix (Fin N) (Fin N) R) p.2 k) * X (p.1, k)) = X := by
    funext p
    simp [Matrix.one_apply, apply_ite C, ite_mul]
  rw [hX, aeval_X_left_apply]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.linSubst_ne_zero {R : Type} [CommRing R] {B N n : ℕ} {M : Matrix (Fin N) (Fin n) R}
    {P : Matrix (Fin n) (Fin N) R} (h : M * P = 1) {f : MvPolynomial (Fin B × Fin N) R} (hf : f ≠ 0) :
    _root_.GlobalTheory.ChowHt.linSubst M f ≠ 0 := by
  intro h0
  apply hf
  have key := _root_.GlobalTheory.HeightUnique.linSubst_linSubst M P f
  rw [h0, h, _root_.GlobalTheory.HeightUnique.linSubst_one] at key
  rw [← key]
  simp [_root_.GlobalTheory.ChowHt.linSubst]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.linSubst_C_mul {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R) (c : R)
    (f : MvPolynomial (Fin B × Fin N) R) :
    _root_.GlobalTheory.ChowHt.linSubst M (C c * f) = C c * _root_.GlobalTheory.ChowHt.linSubst M f := by
  simp [_root_.GlobalTheory.ChowHt.linSubst]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.exists_right_inv {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective w.mulVecLin
    (by rw [Matrix.range_mulVecLin, hw])
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have key := congrArg LinearMap.toMatrix' hg
  have hw' : LinearMap.toMatrix' w.mulVecLin = w := (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, hw'] at key

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma isWeightedHomogeneous_aeval_of_isWeightedHomogeneous {R M σ τ : Type*} [CommSemiring R] [AddCommMonoid M]
    {w : σ → M} {w' : τ → M} {g : σ → MvPolynomial τ R} (hg : ∀ i, IsWeightedHomogeneous w' (g i) (w i))
    {f : MvPolynomial σ R} {m : M} (hf : IsWeightedHomogeneous w f m) :
    IsWeightedHomogeneous w' (aeval g f) m := by
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [aeval_monomial, algebraMap_eq, ← hf (mem_support_iff.mp hd), Finsupp.weight_apply,
    ← zero_add (d.sum fun i c => c • w i)]
  exact (isWeightedHomogeneous_C w' _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun i _ => (hg i).pow (d i))

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.linSubst_homog {R : Type} [Field R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin N) R} (hf : _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) :
    _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a (_root_.GlobalTheory.ChowHt.linSubst M f) := by
  rw [_root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block] at hf ⊢
  unfold _root_.GlobalTheory.Chow.IsBlockHomogeneous at hf ⊢
  unfold _root_.GlobalTheory.ChowHt.linSubst
  refine isWeightedHomogeneous_aeval_of_isWeightedHomogeneous (fun p => ?_) hf
  apply IsWeightedHomogeneous.sum
  intro k _
  have hw : _root_.GlobalTheory.Chow.blockWeight p = _root_.GlobalTheory.Chow.blockWeight ((p.1, k) : Fin B × Fin n) := by
    simp [_root_.GlobalTheory.Chow.blockWeight]
  rw [hw, ← zero_add (_root_.GlobalTheory.Chow.blockWeight ((p.1, k) : Fin B × Fin n))]
  exact (isWeightedHomogeneous_C _ _).mul (isWeightedHomogeneous_X _ _ _)

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.gaussAbs_C {K σ : Type} [Field K] [NumberField K] (w : FinitePlace K) (c : K) :
    _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w (C c : MvPolynomial σ K) = w c := by
  classical
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  by_cases hc : c = 0
  · subst hc
    simp
  · rw [C_apply, support_monomial, if_neg hc]
    simp [Real.coe_toNNReal _ (apply_nonneg w c)]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma gaussAbs_C_mul_of_ne_zero {K σ : Type} [Field K] [NumberField K] (w : FinitePlace K) {c : K}
    (hc : c ≠ 0) (g : MvPolynomial σ K) : _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w (C c * g) = w c * _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w g := by
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  have hs : (C c * g).support = g.support := by
    ext s
    simp [coeff_C_mul, hc]
  rw [hs]
  simp_rw [coeff_C_mul, map_mul, Real.toNNReal_mul (apply_nonneg w c)]
  rw [← NNReal.mul_finset_sup, NNReal.coe_mul, Real.coe_toNNReal _ (apply_nonneg w c)]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma gaussAbs_pos_of_ne_zero {K σ : Type} [Field K] [NumberField K] (w : FinitePlace K)
    {g : MvPolynomial σ K} (hg : g ≠ 0) : 0 < _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w g := by
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hg
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  have h1 : (w (coeff s g)).toNNReal ≤ g.support.sup fun t => (w (coeff t g)).toNNReal :=
    Finset.le_sup (f := fun t => (w (coeff t g)).toNNReal) (mem_support_iff.mpr hs)
  have h2 : 0 < w (coeff s g) := w.pos_iff.mpr hs
  exact_mod_cast lt_of_lt_of_le (Real.toNNReal_pos.mpr h2) h1

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma finsum_log_finitePlace_add_sum_log_norm_embedding {K : Type} [Field K] [NumberField K] {c : K}
    (hc : c ≠ 0) : ∑ᶠ v : FinitePlace K, Real.log (v c) + ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = 0 := by
  rw [_root_.ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq c hc, ← Real.log_finprod (fun v => v.pos_iff.mpr hc), FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv]
  ring

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.formHeight_C_mul {F : Type} [Field F] [NumberField F] {B N n : ℕ} (hN : 0 < N) (δ : ℕ)
    {w : Matrix (Fin N) (Fin n) F} (hw : Submodule.span F (Set.range w.col) = ⊤)
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0) {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) {c : F} (hc : c ≠ 0) :
    _root_.GlobalTheory.ChowHt.formHeight δ w A (C c * f) = _root_.GlobalTheory.ChowHt.formHeight δ w A f := by
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.HeightUnique.exists_right_inv hw
  have hLf : _root_.GlobalTheory.ChowHt.linSubst w f ≠ 0 := _root_.GlobalTheory.HeightUnique.linSubst_ne_zero hP hf
  have hfin : ∀ v : FinitePlace F, Real.log (_root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst w (C c * f))) =
      Real.log (v c) + Real.log (_root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst w f)) := by
    intro v
    rw [_root_.GlobalTheory.HeightUnique.linSubst_C_mul, gaussAbs_C_mul_of_ne_zero v hc,
      Real.log_mul (v.pos_iff.mpr hc).ne' (gaussAbs_pos_of_ne_zero v hLf).ne']
  have harch : ∀ σ : F →+* ℂ, _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst (A σ) (map σ (C c * f))) =
      Real.log ‖σ c‖ + _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst (A σ) (map σ f)) := by
    intro σ
    have hQ : A σ * (A σ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hA σ))
    have hmf : map σ f ≠ 0 := fun h0 => hf (map_injective σ σ.injective (by rw [h0, map_zero]))
    have hg := _root_.GlobalTheory.HeightUnique.linSubst_ne_zero hQ hmf
    have hgh := _root_.GlobalTheory.HeightUnique.linSubst_homog (A σ) (_root_.ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_map_ring a f ha σ)
    have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
    have hC : (C (σ c) : MvPolynomial (Fin B × Fin N) ℂ) ≠ 0 := by simpa using hσc
    have hCh : _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => 0) (C (σ c) : MvPolynomial (Fin B × Fin N) ℂ) :=
      (_root_.ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_iff_forall_weighted_lh0BlockWt _ _).mpr fun _ => isWeightedHomogeneous_C _ _
    rw [map_mul, map_C, _root_.GlobalTheory.HeightUnique.linSubst_C_mul,
      _root_.ReciprocityTheory.MultiplicativeHeights.sphere_mean_mul_multihomogeneous _root_.ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable B N (fun _ => 0) a _ _ hC hg hCh hgh]
    congr 1
    haveI := _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability (B := B) hN
    unfold _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean
    simp [eval_C]
  have hsuppc : (Function.support fun v : FinitePlace F => Real.log (v c)).Finite := by
    simpa [_root_.GlobalTheory.HeightUnique.gaussAbs_C] using _root_.ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite (C c : MvPolynomial Unit F) (by simpa using hc)
  unfold _root_.GlobalTheory.ChowHt.formHeight
  congr 1
  simp_rw [hfin, harch]
  rw [finsum_add_distrib hsuppc (_root_.ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hLf)]
  simp only [Finset.sum_add_distrib]
  linarith [finsum_log_finitePlace_add_sum_log_norm_embedding hc]

end GlobalTheory.HeightUnique
