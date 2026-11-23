import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartMult
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace OrbitChartMult

variable {ι : Type} {n : ι → ℕ}

def chartCone (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) (D : Type*)
    [CommRing D] [Algebra (chartRing x c) D] : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι D :=
  eval₂Hom (Int.castRingHom _) fun p ↦ C (algebraMap (chartRing x c) D (chartEval x c (X p))) * X p.1

def chartIncl (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    chartRing x c →+* AlgebraicClosure ℚ :=
  (ratioField x).val.toRingHom.comp (chartRing x c).val.toRingHom

variable (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))

theorem chartIncl_injective : Function.Injective (chartIncl x c) :=
  fun _ _ h ↦ Subtype.ext (Subtype.ext h)

theorem chartIncl_chartEval_X (p : Coord n) :
    chartIncl x c (chartEval x c (X p)) = x p.1 p.2 / x p.1 (c p.1) := by
  simp [chartIncl, chartEval, chartRatio]

theorem chartEval_X_chart (hc : ∀ k, x k (c k) ≠ 0) (k : ι) :
    chartEval x c (X ⟨k, c k⟩) = 1 := by
  apply chartIncl_injective x c
  rw [chartIncl_chartEval_X, map_one]
  exact div_self (hc k)

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem chartEval_chartMonomial (hc : ∀ k, x k (c k) ≠ 0) (d : ι → ℕ) :
    chartEval x c (chartMonomial c d) = 1 := by
  simp [chartMonomial, map_prod, chartEval_X_chart x c hc]

theorem chartCone_of_isWeightedHomogeneous (D : Type*) [CommRing D] [Algebra (chartRing x c) D]
    {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hF : IsWeightedHomogeneous (coordDeg n) F d) :
    chartCone x c D F = C (algebraMap (chartRing x c) D (chartEval x c F)) * ∏ k, X k ^ d k := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' : ∀ k, ∑ i, m ⟨k, i⟩ = d k := fun k ↦ by
    rw [← weight_coordDeg_apply, hF (mem_support_iff.mp hm)]
  have hε : chartEval x c (monomial m (coeff m F)) =
      algebraMap ℤ _ (coeff m F) * ∏ p, chartEval x c (X p) ^ m p := by
    rw [chartEval, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
    simp only [aeval_X]
  have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι D) ^ m p = ∏ k, X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, (X k : MvPolynomial ι D) ^ m ⟨k, i⟩ = _
    rw [← hm' k, Finset.prod_pow_eq_pow_sum]
  rw [hε, chartCone, coe_eval₂Hom, eval₂_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, eq_intCast,
    map_intCast]
  ring

omit [Fintype ι] [DecidableEq ι] in

theorem chartCone_eq_zero_iff (hc : ∀ k, x k (c k) ≠ 0) (F : MvPolynomial (Coord n) ℤ) :
    chartCone x c (chartRing x c) F = 0 ↔ F ∈ orbitIdeal x := by
  let σ : MvPolynomial ι (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      MvPolynomial ι (AlgebraicClosure ℚ) := aeval fun k ↦ C (x k (c k)) * X k
  let σ' : MvPolynomial ι (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      MvPolynomial ι (AlgebraicClosure ℚ) := aeval fun k ↦ C (x k (c k))⁻¹ * X k
  have hσ : σ'.comp σ = AlgHom.id _ _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [σ, σ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      algebraMap_eq, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  have hσi : Function.Injective σ := fun a b h ↦ by
    have := congrArg σ' h
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hσ, AlgHom.id_apply, AlgHom.id_apply] at this
  have hcomp : (σ.toRingHom.comp (map (chartIncl x c))).comp
      (chartCone x c (chartRing x c)) =
      (Geo.mConeMap (ι := blockIdx n) (flatCone x)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro p
      have h1 : chartIncl x c (chartEval x c (X p)) * x p.1 (c p.1) = x p.1 p.2 := by
        rw [chartIncl_chartEval_X, div_mul_cancel₀ _ (hc p.1)]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chartCone,
        coe_eval₂Hom, eval₂_X, aeval_X,
        map_mul, map_C, map_X, Algebra.algebraMap_self, RingHom.id_apply, Geo.mConeMap, σ, aeval_C,
        algebraMap_eq, flatCone]
      rw [← mul_assoc, ← C_mul, h1]
  have key : ∀ G, σ (map (chartIncl x c) (chartCone x c (chartRing x c) G)) =
      Geo.mConeMap (ι := blockIdx n) (flatCone x) G := fun G ↦ by
    have := congrArg (fun f ↦ f G) hcomp
    simpa using this
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, ← key]
  constructor
  · intro h
    rw [h, map_zero, map_zero]
  · intro h
    refine map_injective _ (chartIncl_injective x c) (hσi ?_)
    rw [h, map_zero, map_zero]

theorem mem_orbitIdeal_of_chartEval_eq_zero (hc : ∀ k, x k (c k) ≠ 0)
    {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hF : IsWeightedHomogeneous (coordDeg n) F d)
    (h0 : chartEval x c F = 0) : F ∈ orbitIdeal x := by
  rw [← chartCone_eq_zero_iff x c hc, chartCone_of_isWeightedHomogeneous x c _ hF, h0]
  simp

attribute [local instance] MvPolynomial.weightedGradedAlgebra in

theorem weightedHomogeneousComponent_mem_of_isMultiHomogIdeal
    {V : Ideal (MvPolynomial (Coord n) ℤ)} (hV : Geo.IsMultiHomogIdeal (ι := blockIdx n) V)
    {v : MvPolynomial (Coord n) ℤ} (hv : v ∈ V) (e : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) e v ∈ V := by
  obtain ⟨S, hS, rfl⟩ := hV
  have hh : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule ℤ (coordDeg n)) :=
    Ideal.homogeneous_span _ S fun f hf ↦ by
      obtain ⟨a, ha⟩ := hS f hf
      exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((geoMultiHomog_iff f a).mp ha)⟩
  exact weightedHomogeneousComponent_mem_of_mem ℤ (coordDeg n) hh hv e

theorem mem_of_chartEval_mem_chartPoint (hc : ∀ k, x k (c k) ≠ 0)
    {V : Ideal (MvPolynomial (Coord n) ℤ)} [hVp : V.IsPrime] (hWV : orbitIdeal x ≤ V)
    (hV : ∀ v ∈ V, ∀ e, weightedHomogeneousComponent (coordDeg n) e v ∈ V)
    (hXV : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hF : IsWeightedHomogeneous (coordDeg n) F d)
    (hFm : chartEval x c F ∈ chartPoint x c V) : F ∈ V := by
  classical
  obtain ⟨v, hv, hvF⟩ := (Ideal.mem_map_iff_of_surjective _ (chartEval_surjective x c)).mp hFm
  have hfin := weightedHomogeneousComponent_finsupp (w := coordDeg n) v
  set S := hfin.toFinset
  have hvsum : v = ∑ e ∈ S, weightedHomogeneousComponent (coordDeg n) e v := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent (w := coordDeg n) v, finsum_eq_sum _ hfin]
  set E : ι → ℕ := d + ∑ e ∈ S, e
  have hdE : d ≤ E := le_self_add
  have heE : ∀ e ∈ S, e ≤ E := fun e he ↦
    (Finset.single_le_sum (f := fun e : ι → ℕ ↦ e) (fun _ _ ↦ zero_le) he).trans le_add_self
  set G := chartMonomial c (E - d) * F -
    ∑ e ∈ S, chartMonomial c (E - e) * weightedHomogeneousComponent (coordDeg n) e v
  have hG : IsWeightedHomogeneous (coordDeg n) G E := by
    rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun e he ↦ ?_)
    · rw [mem_weightedHomogeneousSubmodule]
      simpa [tsub_add_cancel_of_le hdE] using (isWeightedHomogeneous_chartMonomial c (E - d)).mul hF
    · rw [mem_weightedHomogeneousSubmodule]
      simpa [tsub_add_cancel_of_le (heE e he)] using
        (isWeightedHomogeneous_chartMonomial c (E - e)).mul
          (weightedHomogeneousComponent_isWeightedHomogeneous e v)
  have hG0 : chartEval x c G = 0 := by
    simp only [G, map_sub, map_sum, map_mul, chartEval_chartMonomial x c hc, one_mul]
    rw [← map_sum, ← hvsum, hvF, sub_self]
  have hGW := mem_orbitIdeal_of_chartEval_eq_zero x c hc hG hG0
  have hmem : chartMonomial c (E - d) * F ∈ V := by
    have e : chartMonomial c (E - d) * F = G +
        ∑ e ∈ S, chartMonomial c (E - e) * weightedHomogeneousComponent (coordDeg n) e v := by
      simp only [G, sub_add_cancel]
    rw [e]
    exact V.add_mem (hWV hGW) (V.sum_mem fun e _ ↦ V.mul_mem_left _ (hV v hv e))
  have hmon : chartMonomial c (E - d) ∉ V := by
    rw [chartMonomial]
    intro h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hXV k (hVp.mem_of_pow_mem _ hk)
  exact (hVp.mem_or_mem hmem).resolve_left hmon

end OrbitChartMult

end

end GroundTheory.Heights₂.Heights
