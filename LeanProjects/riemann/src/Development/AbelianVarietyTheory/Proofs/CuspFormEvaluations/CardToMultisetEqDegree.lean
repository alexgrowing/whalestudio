import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivMonomialOne

open Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

namespace Jet

variable {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup W'] [NormedSpace ℂ W']

theorem card_toMultiset_eq_degree (m : σ →₀ ℕ) :
    Multiset.card (Finsupp.toMultiset m) = m.degree := by
  simp only [Finsupp.card_toMultiset]
  rfl

theorem degree_eq_of_mem_support {P : MvPolynomial σ ℂ} {a : ℕ} (hP : P.IsHomogeneous a)
    {m : σ →₀ ℕ} (hm : m ∈ P.support) : m.degree = a := by
  by_contra h
  exact (MvPolynomial.mem_support_iff.mp hm) (hP.coeff_eq_zero h)

theorem polyDeriv_eq_sum_monomial (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv P u F x =
      ∑ m ∈ P.support, P.coeff m * polyDeriv (MvPolynomial.monomial m (1 : ℂ)) u F x := by
  simp only [polyDeriv_monomial_one]
  rfl

theorem polyDeriv_add_fun [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W)
    {F G : W → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (x : W) :
    polyDeriv P u (F + G) x = polyDeriv P u F x + polyDeriv P u G x := by
  unfold polyDeriv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_add_apply (contDiff_of_differentiable_fd hF _).contDiffAt
    (contDiff_of_differentiable_fd hG _).contDiffAt]
  simp only [ContinuousMultilinearMap.add_apply]
  ring

theorem polyDeriv_smul_fun [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W)
    {F : W → ℂ} (hF : Differentiable ℂ F) (c : ℂ) (x : W) :
    polyDeriv P u (c • F) x = c * polyDeriv P u F x := by
  unfold polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_const_smul_apply (contDiff_of_differentiable_fd hF _).contDiffAt]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem polyDeriv_sum_fun [FiniteDimensional ℂ W] {κ : Type*} (P : MvPolynomial σ ℂ) (u : σ → W)
    (s : Finset κ) (c : κ → ℂ) (F : κ → W → ℂ) (hF : ∀ i ∈ s, Differentiable ℂ (F i)) (x : W) :
    polyDeriv P u (fun w => ∑ i ∈ s, c i * F i w) x = ∑ i ∈ s, c i * polyDeriv P u (F i) x :=
  ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_sum P u s c F
    (fun i hi k => contDiff_of_differentiable_fd (hF i hi) k) x

theorem polyDeriv_comp_equiv (P : MvPolynomial σ ℂ) (u : σ → W) (F : W' → ℂ) (φ : W ≃L[ℂ] W')
    (x : W) : polyDeriv P u (F ∘ φ) x = polyDeriv P (φ ∘ u) F (φ x) := by
  unfold polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := φ.iteratedFDerivWithin_comp_right F uniqueDiffOn_univ (Set.mem_univ (φ x))
    (Multiset.card (Finsupp.toMultiset m))
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [h]
  rfl

theorem polyDeriv_comp_clm [FiniteDimensional ℂ W'] (P : MvPolynomial σ ℂ) (u : σ → W)
    {F : W' → ℂ} (hF : Differentiable ℂ F) (φ : W →L[ℂ] W') (x : W) :
    polyDeriv P u (F ∘ φ) x = polyDeriv P (φ ∘ u) F (φ x) := by
  unfold polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [φ.iteratedFDeriv_comp_right (contDiff_of_differentiable_fd hF _) x le_rfl]
  rfl

theorem polyDeriv_smul_dir {P : MvPolynomial σ ℂ} {a : ℕ} (hP : P.IsHomogeneous a) (c : ℂ)
    (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv P (fun i => c • u i) F x = c ^ a * polyDeriv P u F x := by
  unfold polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [ContinuousMultilinearMap.map_smul_univ _ (fun _ => c), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  have h : c ^ Multiset.card (Finsupp.toMultiset m) = c ^ a := by
    rw [card_toMultiset_eq_degree, degree_eq_of_mem_support hP hm]
  rw [h]
  ring

theorem polyDeriv_comp_smul_at [FiniteDimensional ℂ W] {P : MvPolynomial σ ℂ} {a : ℕ}
    (hP : P.IsHomogeneous a) (c : ℂ) (u : σ → W) {F : W → ℂ} (hF : Differentiable ℂ F) (x : W) :
    polyDeriv P u (fun v => F (c • v)) x = c ^ a * polyDeriv P u F (c • x) := by
  rw [← polyDeriv_smul_dir hP]
  exact polyDeriv_comp_clm P u hF (c • ContinuousLinearMap.id ℂ W) x

theorem polyDeriv_comp_smul [FiniteDimensional ℂ W] {P : MvPolynomial σ ℂ} {a : ℕ}
    (hP : P.IsHomogeneous a) (c : ℂ) (u : σ → W) {F : W → ℂ} (hF : Differentiable ℂ F) :
    polyDeriv P u (fun v => F (c • v)) 0 = c ^ a * polyDeriv P u F 0 := by
  rw [polyDeriv_comp_smul_at hP c u hF, smul_zero]

section Euclid

variable {ι : Type} [Fintype ι]

theorem Hf_eq_inner (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  simp [Hf, PiLp.inner_apply]

theorem differentiable_translate (q : ℕ) (y : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : Differentiable ℂ F) :
    Differentiable ℂ fun v =>
      cexp (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2) * F (v - y) := by
  have h1 : Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf v y := by
    simp only [Hf_eq_inner]
    exact (innerSL ℂ y).differentiable
  have h2 : Differentiable ℂ fun v : EuclideanSpace ℂ ι => F (v - y) :=
    hF.comp (differentiable_id.sub_const y)
  exact (((h1.const_mul _).sub_const _).cexp).mul h2

theorem norm_translate (q : ℕ) (y : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ)
    (v : EuclideanSpace ℂ ι) :
    ‖cexp (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2) * F (v - y)‖ ^ 2 *
        Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) =
      ‖F (v - y)‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v - y‖ ^ 2) := by
  have hre : (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2 : ℂ).re =
      q * Real.pi * (inner ℂ y v : ℂ).re - q * Real.pi * ‖y‖ ^ 2 / 2 := by
    rw [Hf_eq_inner, Hf_eq_inner, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hn : ‖v - y‖ ^ 2 = ‖y‖ ^ 2 - 2 * (inner ℂ y v : ℂ).re + ‖v‖ ^ 2 := by
    rw [norm_sub_rev, @norm_sub_sq ℂ]
    rfl
  rw [norm_mul, Complex.norm_exp, hre, hn, mul_pow, mul_comm _ (‖F (v - y)‖ ^ 2), mul_assoc,
    ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  push_cast
  ring

open Classical in

theorem norm_polyDeriv_le (q : ℕ) (hq : 1 ≤ q) (F : EuclideanSpace ℂ ι → ℂ)
    (hF : Differentiable ℂ F) (S : ℝ)
    (hS : ∀ v, ‖F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤ S) (P : MvPolynomial ι ℂ) (a : ℕ)
    (hP : P.IsHomogeneous a) :
    ‖polyDeriv P (fun i => EuclideanSpace.single i 1) F 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * Real.sqrt S *
        (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set t : ℝ := Real.sqrt q with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hq0
  have ht2 : t ^ 2 = q := Real.sq_sqrt hq0.le
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  set G : EuclideanSpace ℂ ι → ℂ := fun v => F ((t : ℂ)⁻¹ • v) with hGdef
  have hG : Differentiable ℂ G := hF.comp (g := F) (f := fun v => (t : ℂ)⁻¹ • v) (by fun_prop)
  have hGS : ∀ v, ‖G v‖ ^ 2 * Real.exp (-Real.pi * ‖v‖ ^ 2) ≤ S := by
    intro v
    have h := hS ((t : ℂ)⁻¹ • v)
    have e : -(q * Real.pi) * ‖(t : ℂ)⁻¹ • v‖ ^ 2 = -Real.pi * ‖v‖ ^ 2 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0.le, mul_pow, inv_pow, ht2]
      field_simp
    rwa [e] at h
  have hFG : F = fun v => G ((t : ℂ) • v) := by
    funext v
    simp only [hGdef, smul_smul, inv_mul_cancel₀ htc, one_smul]
  have hb : ‖polyDeriv P (fun i => EuclideanSpace.single i 1) G 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.sqrt S *
        (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2)) := by
    rw [polyDeriv_eq_sum_monomial, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := gCauchy ι G hG S hGS m
    rwa [degree_eq_of_mem_support hP hm] at h
  have hpow : t ^ a = (q : ℝ) ^ ((a : ℝ) / 2) := by
    rw [ht, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  have hsplit : ((q : ℝ) * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) =
      t ^ a * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
    rw [hpow, ← Real.mul_rpow hq0.le (by positivity)]
    congr 1
    ring
  rw [hFG, polyDeriv_comp_smul hP _ _ hG, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg ht0.le, hsplit]
  calc t ^ a * ‖polyDeriv P (fun i => EuclideanSpace.single i 1) G 0‖
      ≤ t ^ a * ((∑ m ∈ P.support, ‖P.coeff m‖) * (Real.sqrt S *
        (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end Euclid

end Jet

open Classical in

theorem translate_jet_bound {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (q : ℕ) (hq : 1 ≤ q) (F : EuclideanSpace ℂ ι → ℂ) (hF : Differentiable ℂ F) (S : ℝ)
    (hS : ∀ v, ‖F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤ S) (P : MvPolynomial ι ℂ) (a : ℕ) (hP : P.IsHomogeneous a) (y : EuclideanSpace ℂ ι) :
    ‖polyDeriv P (fun i => EuclideanSpace.single i 1) (U q y F) 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * Real.sqrt S * (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
  have hfun : U q y F = fun v =>
      cexp (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2) * F (v - y) := funext (hU q y F)
  rw [hfun]
  refine Jet.norm_polyDeriv_le q hq _ (Jet.differentiable_translate q y hF) S (fun v => ?_) P a hP
  rw [Jet.norm_translate]
  exact hS _

end GlobalTheory
