import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartMax
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PSubringPrimeMaximal
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace OrbitChartMax

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def dehomCoords {Ω : Type*} [Field Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1)) :
    Coord n → Ω :=
  fun p ↦ (z ⟨p.1, c p.1⟩)⁻¹ * z p

theorem aeval_mul_of_homog {R : Type*} [CommRing R] [Algebra ℤ R] (t : ι → R) (z : Coord n → R)
    {G : MvPolynomial (Coord n) ℤ} {b : ι → ℕ} (hG : IsWeightedHomogeneous (coordDeg n) G b) :
    aeval (fun p ↦ t p.1 * z p) G = aeval z G * ∏ k, t k ^ b k := by
  classical
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hmb : ∀ k, ∑ i, m ⟨k, i⟩ = b k := fun k ↦ by
    rw [← weight_coordDeg_apply, hG (mem_support_iff.mp hm)]
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, mul_comm]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← hmb k]
  exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ m ⟨k, i⟩) (t k)

def homDeg (F : MvPolynomial (Coord n) ℤ) : ι → ℕ :=
  fun k ↦ F.support.sup fun m ↦ Finsupp.weight (coordDeg n) m k

def homogenize (c : (k : ι) → Fin (n k + 1)) (F : MvPolynomial (Coord n) ℤ) :
    MvPolynomial (Coord n) ℤ :=
  ∑ m ∈ F.support, monomial m (coeff m F) *
    chartMonomial c (homDeg F - Finsupp.weight (coordDeg n) m)

theorem isWeightedHomogeneous_homogenize (c : (k : ι) → Fin (n k + 1))
    (F : MvPolynomial (Coord n) ℤ) :
    IsWeightedHomogeneous (coordDeg n) (homogenize c F) (homDeg F) := by
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm ↦ ?_
  have hle : Finsupp.weight (coordDeg n) m ≤ homDeg F := fun k ↦
    Finset.le_sup (f := fun m ↦ Finsupp.weight (coordDeg n) m k) hm
  have h := (isWeightedHomogeneous_monomial (coordDeg n) m (coeff m F) rfl).mul
    (isWeightedHomogeneous_chartMonomial c (homDeg F - Finsupp.weight (coordDeg n) m))
  rwa [add_tsub_cancel_of_le hle] at h

theorem map_homogenize {R : Type*} [CommRing R] (c : (k : ι) → Fin (n k + 1))
    (φ : MvPolynomial (Coord n) ℤ →+* R) (hφ : ∀ k, φ (X ⟨k, c k⟩) = 1)
    (F : MvPolynomial (Coord n) ℤ) : φ (homogenize c F) = φ F := by
  conv_rhs => rw [F.as_sum]
  simp only [homogenize, map_sum, map_mul, chartMonomial, map_prod, map_pow, hφ, one_pow,
    Finset.prod_const_one, mul_one]

theorem aeval_dehomCoords {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) (F : MvPolynomial (Coord n) ℤ) :
    aeval (dehomCoords z c) F =
      aeval z (homogenize c F) * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ homDeg F k := by
  change (aeval (dehomCoords z c)).toRingHom F = _
  rw [← map_homogenize c (aeval (dehomCoords z c)).toRingHom (fun k ↦ by
    simp [dehomCoords, inv_mul_cancel₀ (hz k)]) F]
  exact aeval_mul_of_homog (fun k ↦ (z ⟨k, c k⟩)⁻¹) z (isWeightedHomogeneous_homogenize c F)

omit [DecidableEq ι] in

theorem prod_inv_pow_ne_zero {Ω : Type*} [Field Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) (D : ι → ℕ) : ∏ k, (z ⟨k, c k⟩)⁻¹ ^ D k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (inv_ne_zero (hz k))

theorem mem_orbitIdeal_of_aeval_eq_zero (x : Cone n (AlgebraicClosure ℚ))
    {G : MvPolynomial (Coord n) ℤ} {b : ι → ℕ} (hG : IsWeightedHomogeneous (coordDeg n) G b)
    (h0 : aeval (flatCone x) G = 0) : G ∈ orbitIdeal x := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap]
  have e : (fun p : Coord n ↦ C (flatCone x p) * (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ))) =
      fun p ↦ (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ)) * C (flatCone x p) :=
    funext fun p ↦ mul_comm _ _
  have hC : aeval (fun p : Coord n ↦ (C (flatCone x p) : MvPolynomial ι (AlgebraicClosure ℚ))) G =
      C (aeval (flatCone x) G) := by
    rw [aeval_def, aeval_def, eval₂_comp_left]
    congr 1
  change aeval (fun p : Coord n ↦ C (flatCone x p) * (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ))) G = 0
  have h := aeval_mul_of_homog (fun k : ι ↦ (X k : MvPolynomial ι (AlgebraicClosure ℚ)))
    (fun p ↦ C (flatCone x p)) hG
  beta_reduce at h
  rw [e]
  refine h.trans (mul_eq_zero_of_left (hC.trans ?_) _)
  rw [h0, map_zero]

theorem aeval_dehomCoords_of_homog {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (z : Coord n → Ω)
    (c : (k : ι) → Fin (n k + 1)) {G : MvPolynomial (Coord n) ℤ} {b : ι → ℕ}
    (hG : IsWeightedHomogeneous (coordDeg n) G b) :
    aeval (dehomCoords z c) G = aeval z G * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ b k :=
  aeval_mul_of_homog (fun k ↦ (z ⟨k, c k⟩)⁻¹) z hG

omit [Fintype ι] [DecidableEq ι] in

theorem val_comp_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    (chartRing x c).val.comp (chartEval x c) = aeval (chartRatio x c) :=
  MvPolynomial.algHom_ext fun _ ↦ by simp [chartEval]

omit [Fintype ι] [DecidableEq ι] in

theorem chartEval_surjective (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Function.Surjective (chartEval x c) := by
  rintro ⟨u, hu⟩
  have hu' := hu
  rw [chartRing, Algebra.adjoin_range_eq_range_aeval] at hu'
  obtain ⟨F, hF⟩ := hu'
  exact ⟨F, Subtype.ext ((DFunLike.congr_fun (val_comp_chartEval x c) F).trans hF)⟩

omit [Fintype ι] [DecidableEq ι] in

theorem coe_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (F : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c F : ratioField x) : AlgebraicClosure ℚ)) =
      aeval (dehomCoords (flatCone x) c) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, Subalgebra.coe_add, IntermediateField.coe_add, hp, hq, map_add]
  | mul_X p q hp =>
    rw [map_mul, Subalgebra.coe_mul, IntermediateField.coe_mul, hp, map_mul]
    simp [chartEval, chartRatio, dehomCoords, flatCone, div_eq_inv_mul]

omit [Fintype ι] [DecidableEq ι] in

theorem chartEval_eq_zero_iff (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (F : MvPolynomial (Coord n) ℤ) :
    chartEval x c F = 0 ↔ aeval (dehomCoords (flatCone x) c) F = 0 := by
  rw [← coe_chartEval, ZeroMemClass.coe_eq_zero, ZeroMemClass.coe_eq_zero]

omit [Fintype ι] [DecidableEq ι] in

theorem chartEval_X_chart (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hxc : ∀ k, flatCone x ⟨k, c k⟩ ≠ 0) (k : ι) : chartEval x c (X ⟨k, c k⟩) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_chartEval]
  simp [dehomCoords, inv_mul_cancel₀ (hxc k)]

section Generic

variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]

omit [Fintype ι] [DecidableEq ι] in

def genPt : Coord n → FractionRing (MvPolynomial (Coord n) ℤ ⧸ V) :=
  fun p ↦ algebraMap _ _ (Ideal.Quotient.mk V (X p))

omit [Fintype ι] [DecidableEq ι] [V.IsPrime] in

theorem aeval_genPt (F : MvPolynomial (Coord n) ℤ) :
    aeval (genPt V) F = algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))
      (Ideal.Quotient.mk V F) := by
  have h : (aeval (genPt V)).toRingHom =
      (algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))).comp (Ideal.Quotient.mk V) :=
    MvPolynomial.ringHom_ext (fun a ↦ RingHom.congr_fun (RingHom.ext_int
      ((aeval (genPt V)).toRingHom.comp C)
      (((algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))).comp
        (Ideal.Quotient.mk V)).comp C)) a)
      (fun p ↦ by simp [genPt])
  exact DFunLike.congr_fun h F

omit [Fintype ι] [DecidableEq ι] [V.IsPrime] in

theorem aeval_genPt_eq_zero_iff (F : MvPolynomial (Coord n) ℤ) : aeval (genPt V) F = 0 ↔ F ∈ V := by
  rw [aeval_genPt, map_eq_zero_iff _ (IsFractionRing.injective _ _),
    Ideal.Quotient.eq_zero_iff_mem]

omit [Fintype ι] [DecidableEq ι] [V.IsPrime] in

theorem genPt_ne_zero {p : Coord n} (hp : (X p : MvPolynomial (Coord n) ℤ) ∉ V) : genPt V p ≠ 0 := by
  have h := (aeval_genPt_eq_zero_iff V (X p)).not.mpr hp
  rwa [aeval_X] at h

end Generic

theorem proof : Statement := by
  intro ι _ _ _ n A x s hx hs V hV c hc
  obtain ⟨hVmin, -⟩ := hV
  have : V.IsPrime := hVmin.1.1
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hsV : s ∈ V := hVmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨a, -, hsa, hsP⟩ := hs
  have hsa' : IsWeightedHomogeneous (coordDeg n) s a := (geoMultiHomog_iff s a).mp hsa

  have hVh : ∀ f ∈ V, ∀ b, weightedHomogeneousComponent (coordDeg n) b f ∈ V := by
    have hJ : NumbersDVR.IsMultiHomogIdeal (ι := blockIdx n) (orbitIdeal x ⊔ Ideal.span {s}) := by
      intro f hf b
      obtain ⟨p, hp, t, ht, rfl⟩ := Submodule.mem_sup.mp hf
      rw [map_add]
      exact Submodule.add_mem_sup (OrbitCurve.weightedHomogeneousComponent_mem_orbitIdeal x hp b)
        (NumbersDVR.isMultiHomogIdeal_span_singleton (e := a) hsa' t ht b)
    exact NumbersDVR.MinimalPrimeMultiHomog.proof ℤ ι (blockIdx n) _ V hJ hVmin

  have hxc : ∀ k, flatCone x ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    refine hc k (hPV ?_)
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [h0]
  have hyc : ∀ k, genPt V ⟨k, c k⟩ ≠ 0 := fun k ↦ genPt_ne_zero V (hc k)

  have hVzero : ∀ f ∈ V, aeval (dehomCoords (genPt V) c) f = 0 := by
    intro f hf
    classical
    rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    exact (aeval_dehomCoords_of_homog (genPt V) c
      (weightedHomogeneousComponent_isWeightedHomogeneous b f)).trans
      (mul_eq_zero_of_left ((aeval_genPt_eq_zero_iff V _).mpr (hVh f hf b)) _)

  have hker : ∀ F, chartEval x c F = 0 → aeval (dehomCoords (genPt V) c) F = 0 := by
    intro F hF
    rw [chartEval_eq_zero_iff] at hF
    have hF' := (aeval_dehomCoords (flatCone x) c hxc F).symm.trans hF
    have hH := (mul_eq_zero.mp hF').resolve_right (prod_inv_pow_ne_zero _ c hxc _)
    have hHV : homogenize c F ∈ V :=
      hPV (mem_orbitIdeal_of_aeval_eq_zero x (isWeightedHomogeneous_homogenize c F) hH)
    exact (aeval_dehomCoords (genPt V) c hyc F).trans
      (mul_eq_zero_of_left ((aeval_genPt_eq_zero_iff V _).mpr hHV) _)

  have hmem : ∀ F, chartEval x c F ∈ chartPoint x c V ↔
      aeval (dehomCoords (genPt V) c) F = 0 := by
    intro F
    constructor
    · intro hF
      obtain ⟨v, hv, hvF⟩ :=
        (Ideal.mem_map_iff_of_surjective _ (chartEval_surjective x c)).mp hF
      have h1 := hker (F - v) (by rw [map_sub, hvF, sub_self])
      rwa [map_sub, hVzero v hv, sub_zero] at h1
    · intro hF
      have hF' := (aeval_dehomCoords (genPt V) c hyc F).symm.trans hF
      have hH := (aeval_genPt_eq_zero_iff V _).mp
        ((mul_eq_zero.mp hF').resolve_right (prod_inv_pow_ne_zero _ c hyc _))
      have e : chartEval x c (homogenize c F) = chartEval x c F :=
        map_homogenize c (chartEval x c).toRingHom (chartEval_X_chart x c hxc) F
      rw [← e]
      exact Ideal.mem_map_of_mem _ hH
  have hprime : (chartPoint x c V).IsPrime := by
    refine ⟨fun htop ↦ ?_, fun {u v} huv ↦ ?_⟩
    · have h1 : chartEval x c 1 ∈ chartPoint x c V := by rw [htop]; exact Submodule.mem_top
      rw [hmem, map_one] at h1
      exact one_ne_zero h1
    · obtain ⟨F, rfl⟩ := chartEval_surjective x c u
      obtain ⟨G, rfl⟩ := chartEval_surjective x c v
      rw [← map_mul, hmem, map_mul] at huv
      rcases mul_eq_zero.mp huv with h | h
      · exact Or.inl ((hmem F).mpr h)
      · exact Or.inr ((hmem G).mpr h)
  have hne : chartPoint x c V ≠ ⊥ := by
    intro hbot
    have h1 : chartEval x c s ∈ chartPoint x c V := Ideal.mem_map_of_mem _ hsV
    rw [hbot, Ideal.mem_bot, chartEval_eq_zero_iff] at h1
    have h2 := (aeval_dehomCoords_of_homog (flatCone x) c hsa').symm.trans h1
    exact hsP (mem_orbitIdeal_of_aeval_eq_zero x hsa'
      ((mul_eq_zero.mp h2).resolve_right (prod_inv_pow_ne_zero _ c hxc _)))
  exact SubringPrimeMaximal.proof (ratioField x) (chartRing x c) _ hprime hne

end OrbitChartMax

end

end GroundTheory.Heights₂.Heights
