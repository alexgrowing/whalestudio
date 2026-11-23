import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.UnitsBasic
import GroundTheory.LocalFields.UnitsPowers
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter Polynomial
open scoped WithZero nonZeroDivisors

section Fields

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

def normUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K : L →* K)

variable {K L} in
@[simp]
theorem coe_normUnits (x : Lˣ) : ((normUnits K L x : Kˣ) : K) = Algebra.norm K (x : L) :=
  rfl

theorem algebraMap_norm_eq_prod [FiniteDimensional K L] [IsGalois K L] (x : L) :
    algebraMap K L (Algebra.norm K x) = ∏ σ : L ≃ₐ[K] L, σ x :=
  Algebra.norm_eq_prod_automorphisms K x

end Fields

section Ord

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem ord_zpow {x : K} (hx : x ≠ 0) (k : ℤ) : ord (x ^ k) = k * ord x := by
  have h1 := normalizedValuation_eq_exp_ord (zpow_ne_zero k hx)
  rw [map_zpow₀, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zsmul, WithZero.exp_inj,
    smul_eq_mul] at h1
  linear_combination h1

theorem ord_pow {x : K} (hx : x ≠ 0) (k : ℕ) : ord (x ^ k) = k * ord x := by
  simpa using ord_zpow hx k

@[simp]
theorem ord_zero : ord (0 : K) = 0 := by
  simp [ord]

theorem ord_unitsOfIntProd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (n : Multiplicative ℤ)
    (u : 𝒪[K]ˣ) : ord ((unitsOfIntProd hϖ (n, u) : Kˣ) : K) = n.toAdd := by
  simp [ord, normalizedValuation_unitsOfIntProd]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem unitsOfIntProd_eq {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (n : Multiplicative ℤ)
    (u : 𝒪[K]ˣ) : unitsOfIntProd hϖ (n, u) = uniformizerUnit hϖ ^ n.toAdd * unitsIncl K u := by
  simp [unitsOfIntProd, zpowersHom_apply]

theorem ord_eq_zero_iff_mem {x : Kˣ} : ord (x : K) = 0 ↔ x ∈ unitFiltrationUnits K 0 := by
  rw [mem_unitFiltrationUnits_zero_iff, ← map_one (valuation K), ← normalizedValuation_eq_iff,
    normalizedValuation_eq_exp_ord x.ne_zero, map_one, ← WithZero.exp_zero, WithZero.exp_inj,
    neg_eq_zero]

theorem setOf_ord_eq {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (m : ℤ) :
    {y : Kˣ | ord (y : K) = m} =
      (Homeomorph.mulLeft (uniformizerUnit hϖ ^ (-m))) ⁻¹' (unitFiltrationUnits K 0 : Set Kˣ) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Homeomorph.coe_mulLeft, SetLike.mem_coe,
    ← ord_eq_zero_iff_mem, Units.val_mul, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  rw [ord_mul (zpow_ne_zero _ hϖ0) y.ne_zero, ord_zpow hϖ0, ord_uniformizer hϖ]
  omega

theorem isOpen_setOf_ord_eq (m : ℤ) : IsOpen {y : Kˣ | ord (y : K) = m} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [setOf_ord_eq hϖ]
  exact (isOpen_unitFiltrationUnits 0).preimage (Homeomorph.continuous _)

theorem isCompact_setOf_ord_eq (m : ℤ) : IsCompact {y : Kˣ | ord (y : K) = m} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [setOf_ord_eq hϖ, Homeomorph.isCompact_preimage]
  exact isCompact_unitFiltrationUnits 0

variable (K) in

instance locallyCompactSpace_units : LocallyCompactSpace Kˣ :=
  (isCompact_unitFiltrationUnits 0).locallyCompactSpace_of_mem_nhds_of_group
    ((isOpen_unitFiltrationUnits 0).mem_nhds (Subgroup.one_mem _))

end Ord

section Local

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isLocalization_integer :
    IsLocalization (Algebra.algebraMapSubmonoid 𝒪[L] 𝒪[K]⁰) L :=
  IsIntegralClosure.isLocalization 𝒪[K] K L 𝒪[L]

variable {K L}

theorem coe_norm_integer (x : 𝒪[L]) :
    ((Algebra.norm 𝒪[K] x : 𝒪[K]) : K) = Algebra.norm K (x : L) := by
  have := isLocalization_integer K L
  exact (Algebra.norm_localization (Rₘ := K) (Sₘ := L) 𝒪[K] 𝒪[K]⁰ x).symm

theorem coe_trace_integer (x : 𝒪[L]) :
    ((Algebra.trace 𝒪[K] 𝒪[L] x : 𝒪[K]) : K) = Algebra.trace K L (x : L) := by
  have := isLocalization_integer K L
  exact (Algebra.trace_localization (Rₘ := K) (Sₘ := L) 𝒪[K] 𝒪[K]⁰ x).symm

theorem norm_mem_integer {x : L} (hx : x ∈ 𝒪[L]) : Algebra.norm K x ∈ 𝒪[K] := by
  have h := coe_norm_integer (K := K) (⟨x, hx⟩ : 𝒪[L])
  rw [← h]
  exact (Algebra.norm 𝒪[K] (⟨x, hx⟩ : 𝒪[L])).2

variable (K L) in

def normIntegerUnits : 𝒪[L]ˣ →* 𝒪[K]ˣ :=
  Units.map (Algebra.norm 𝒪[K] : 𝒪[L] →* 𝒪[K])

theorem coe_normIntegerUnits (u : 𝒪[L]ˣ) :
    (((normIntegerUnits K L u : 𝒪[K]ˣ) : 𝒪[K]) : K) = Algebra.norm K ((u : 𝒪[L]) : L) :=
  coe_norm_integer _

theorem normUnits_unitsIncl (u : 𝒪[L]ˣ) :
    normUnits K L (unitsIncl L u) = unitsIncl K (normIntegerUnits K L u) := by
  ext
  simp [coe_normIntegerUnits]

theorem map_normUnits_unitFiltrationUnits_zero_le :
    (unitFiltrationUnits L 0).map (normUnits K L) ≤ unitFiltrationUnits K 0 := by
  rintro _ ⟨_, ⟨u, -, rfl⟩, rfl⟩
  exact ⟨normIntegerUnits K L u, by simp, (normUnits_unitsIncl u).symm⟩

section Valuation

theorem ord_algebraMap_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ord (algebraMap K L (ϖ : K)) = ramificationIndex K L := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have h := map_maximalIdeal K L
  rw [hϖ.maximalIdeal_eq, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h.symm
  have h2 : algebraMap K L (ϖ : K) = (π : L) ^ ramificationIndex K L * ((u : 𝒪[L]) : L) := by
    rw [← coe_algebraMap_integer, ← hu]
    push_cast
    rfl
  have hπ0 : (π : L) ≠ 0 := by exact_mod_cast hπ.ne_zero
  rw [h2, ord_mul (pow_ne_zero _ hπ0) (by simp), ord_pow hπ0, ord_uniformizer hπ, ord_unit]
  simp

theorem ord_algebraMap (a : K) : ord (algebraMap K L a) = ramificationIndex K L * ord a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨⟨n, u⟩, hx⟩ := (unitsOfIntProd_bijective hϖ).2 (Units.mk0 a ha)
  have ha' : a = (ϖ : K) ^ n.toAdd * ((u : 𝒪[K]) : K) := by
    rw [← coe_unitsOfIntProd hϖ, hx, Units.val_mk0]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  have hϖL : algebraMap K L (ϖ : K) ≠ 0 := by simpa using hϖ0
  have hu : algebraMap K L ((u : 𝒪[K]) : K) =
      (((Units.map (algebraMap 𝒪[K] 𝒪[L]).toMonoidHom u : 𝒪[L]ˣ) : 𝒪[L]) : L) := rfl
  rw [ha', map_mul, map_zpow₀, ord_mul (zpow_ne_zero _ hϖL) (by rw [hu]; simp), ord_zpow hϖL,
    ord_algebraMap_uniformizer hϖ, hu, ord_unit, ord_mul (zpow_ne_zero _ hϖ0) (by simp),
    ord_zpow hϖ0, ord_uniformizer hϖ, ord_unit]
  ring

theorem ord_norm_units {π : 𝒪[L]} (hπ : Irreducible π) (x : Lˣ) :
    ord (Algebra.norm K (x : L)) = ord (x : L) * ord (Algebra.norm K (π : L)) := by
  obtain ⟨⟨n, u⟩, rfl⟩ := (unitsOfIntProd_bijective hπ).2 x
  rw [ord_unitsOfIntProd, ← coe_normUnits, unitsOfIntProd_eq, map_mul, map_zpow,
    normUnits_unitsIncl, Units.val_mul, Units.val_zpow_eq_zpow_val, coe_unitsIncl,
    ord_mul (zpow_ne_zero _ (Units.ne_zero _)) (by simp), ord_zpow (Units.ne_zero _), ord_unit,
    coe_normUnits, coe_uniformizerUnit]
  ring

theorem ord_norm_uniformizer {π : 𝒪[L]} (hπ : Irreducible π) :
    ord (Algebra.norm K (π : L)) = residueDegree K L := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  have hϖL : algebraMap K L (ϖ : K) ≠ 0 := by simpa using hϖ0
  have h := ord_norm_units (K := K) hπ (Units.mk0 _ hϖL)
  rw [Units.val_mk0, Algebra.norm_algebraMap, ord_pow hϖ0, ord_uniformizer hϖ,
    ord_algebraMap_uniformizer hϖ, ← ramificationIndex_mul_residueDegree K L] at h
  have he : (ramificationIndex K L : ℤ) ≠ 0 := by
    exact_mod_cast (ramificationIndex_pos K L).ne'
  push_cast at h
  exact (mul_left_cancel₀ he (by linear_combination h)).symm

theorem ord_norm (x : L) : ord (Algebra.norm K x) = residueDegree K L * ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have := ord_norm_units (K := K) hπ (Units.mk0 x hx)
  rw [Units.val_mk0, ord_norm_uniformizer hπ] at this
  rw [this, mul_comm]

theorem ord_algebraMap_norm (x : L) :
    ord (algebraMap K L (Algebra.norm K x)) = Module.finrank K L * ord x := by
  rw [ord_algebraMap, ord_norm, ← ramificationIndex_mul_residueDegree K L]
  push_cast
  ring

end Valuation

section Topology

variable (K L)

theorem continuous_algebraNorm : Continuous (Algebra.norm K : L → K) := by
  classical
  have := isModuleTopology K L
  let b := Module.finBasis K L
  have hlin : Continuous (Algebra.leftMulMatrix b : L → Matrix _ _ K) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h : (Algebra.norm K : L → K) = fun x ↦ (Algebra.leftMulMatrix b x).det := by
    funext x
    exact Algebra.norm_eq_matrix_det b x
  rw [h]
  exact hlin.matrix_det

theorem continuous_normUnits : Continuous (normUnits K L) := by
  rw [Units.continuous_iff]
  refine ⟨(continuous_algebraNorm K L).comp Units.continuous_val, ?_⟩
  have h : (fun x : Lˣ ↦ (((normUnits K L x)⁻¹ : Kˣ) : K)) =
      fun x ↦ Algebra.norm K ((x⁻¹ : Lˣ) : L) := by
    funext x
    rw [← map_inv, coe_normUnits]
  rw [h]
  exact (continuous_algebraNorm K L).comp Units.continuous_coe_inv

theorem isProperMap_normUnits : IsProperMap (normUnits K L) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_normUnits K L, fun C hC ↦ ?_⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun m : ℤ ↦ {y : Kˣ | ord (y : K) = m})
    isOpen_setOf_ord_eq (fun y _ ↦ Set.mem_iUnion.2 ⟨_, rfl⟩)
  refine IsCompact.of_isClosed_subset
    (t.isCompact_biUnion fun m _ ↦ isCompact_setOf_ord_eq (m / residueDegree K L))
    (hC.isClosed.preimage (continuous_normUnits K L)) ?_
  intro x hx
  obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.1 (ht hx)
  refine Set.mem_iUnion₂.2 ⟨m, hm, ?_⟩
  simp only [Set.mem_ofPred_eq, coe_normUnits, ord_norm] at hxm ⊢
  have hf : (residueDegree K L : ℤ) ≠ 0 := by exact_mod_cast (residueDegree_pos K L).ne'
  rw [← hxm, Int.mul_ediv_cancel_left _ hf]

theorem isClosed_range_normUnits : IsClosed ((normUnits K L).range : Set Kˣ) := by
  rw [MonoidHom.coe_range]
  exact (isProperMap_normUnits K L).isClosedMap.isClosed_range

end Topology

theorem exists_norm_one_add_smul_eq (z : 𝒪[L]) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (k : ℕ)
    (ε : 𝒪[K]ˣ) (hz : Algebra.trace 𝒪[K] 𝒪[L] z = ϖ ^ k * ε) (a : 𝒪[K])
    (ha : ϖ ^ (2 * k + 1) ∣ 1 - a) : ∃ r : 𝒪[K], Algebra.norm 𝒪[K] (1 + r • z) = a := by
  classical
  let b := Module.Free.chooseBasis 𝒪[K] 𝒪[L]
  set M := Algebra.leftMulMatrix b z with hM
  set Q := (Matrix.det (1 + (X : 𝒪[K][X]) • M.map C)).divX.divX with hQ
  let f : 𝒪[K][X] := C (1 - a) + C M.trace * X + Q * X ^ 2
  have hnorm : ∀ r : 𝒪[K], Algebra.norm 𝒪[K] (1 + r • z) = 1 + M.trace * r + Q.eval r * r ^ 2 := by
    intro r
    rw [Algebra.norm_eq_matrix_det b, map_add, map_one, map_smul, Matrix.det_one_add_smul]
  have htr : M.trace = ϖ ^ k * ε := by
    rw [← hz, Algebra.trace_eq_matrix_trace b]
  have hd : f.derivative.eval 0 = ϖ ^ k * ε := by
    simp [f, htr]
  have hf0 : f.eval 0 = 1 - a := by
    simp [f]
  obtain ⟨r, hr, -⟩ := exists_root_of_dvd hϖ f 0 k ε hd (by rwa [hf0])
  refine ⟨r, ?_⟩
  rw [hnorm]
  have h0 : f.eval r = 0 := hr
  simp only [f, eval_add, eval_C, eval_mul, eval_X, eval_pow] at h0
  linear_combination h0

section Separable

variable [Algebra.IsSeparable K L]

variable (K L) in

theorem exists_trace_integer_ne_zero : ∃ z : 𝒪[L], Algebra.trace 𝒪[K] 𝒪[L] z ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w : L, Algebra.trace K L w ≠ 0 := by
    by_contra h
    refine one_ne_zero ((traceForm_nondegenerate K L).1 1 fun w ↦ ?_)
    simp only [not_exists, not_not] at h
    simpa using h w
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h1 : valuation L (algebraMap K L (ϖ : K)) < 1 :=
    (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) _).mpr
      (valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ))
  have hv0 : valuation L w ≠ 0 := by simpa using hw0
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 (valuation L w)⁻¹ (inv_ne_zero hv0))
  have hint : algebraMap K L (ϖ : K) ^ m * w ∈ 𝒪[L] := by
    rw [Valuation.mem_integer_iff, map_mul, map_pow]
    calc valuation L (algebraMap K L (ϖ : K)) ^ m * valuation L w
        ≤ (valuation L w)⁻¹ * valuation L w := by
          gcongr
          exact hm.le
      _ = 1 := inv_mul_cancel₀ hv0
  refine ⟨⟨_, hint⟩, fun h ↦ ?_⟩
  have h2 : Algebra.trace K L (algebraMap K L (ϖ : K) ^ m * w) = 0 := by
    have h3 := coe_trace_integer (K := K) (⟨_, hint⟩ : 𝒪[L])
    rw [h, ZeroMemClass.coe_zero] at h3
    exact h3.symm
  rw [← map_pow, ← Algebra.smul_def, map_smul, smul_eq_mul] at h2
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact mul_ne_zero (pow_ne_zero _ hϖ0) hw h2

variable (K L) in

theorem exists_unitFiltrationUnits_le_range_normUnits :
    ∃ n, unitFiltrationUnits K n ≤ (normUnits K L).range := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨z, hz⟩ := exists_trace_integer_ne_zero K L
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hz hϖ
  obtain ⟨ε, hε⟩ := hk.symm
  refine ⟨2 * k + 1, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hdvd : ϖ ^ (2 * k + 1) ∣ 1 - (a : 𝒪[K]) := by
    rw [← dvd_neg, neg_sub]
    exact (mem_maximalIdeal_pow_iff hϖ).mp ha
  obtain ⟨r, hr⟩ := exists_norm_one_add_smul_eq z hϖ k ε hε.symm a hdvd
  have hN := coe_norm_integer (K := K) (1 + r • z)
  rw [hr] at hN
  have hne : ((1 + r • z : 𝒪[L]) : L) ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hN
    simp at hN
  refine ⟨Units.mk0 _ hne, ?_⟩
  ext
  rw [coe_normUnits, Units.val_mk0, ← hN, coe_unitsIncl]

variable (K L) in

theorem isOpen_range_normUnits : IsOpen ((normUnits K L).range : Set Kˣ) := by
  obtain ⟨n, hn⟩ := exists_unitFiltrationUnits_le_range_normUnits K L
  exact Subgroup.isOpen_mono hn (isOpen_unitFiltrationUnits n)

variable (K L) in

theorem finiteIndex_range_normUnits : (normUnits K L).range.FiniteIndex := by
  obtain ⟨n, hn⟩ := exists_unitFiltrationUnits_le_range_normUnits K L
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set d := Module.finrank K L with hd
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  let P : Subgroup (Multiplicative ℤ × 𝒪[K]ˣ) :=
    (AddSubgroup.zmultiples (d : ℤ)).toSubgroup.prod (unitFiltration K n)
  have hP : P.index ≠ 0 := by
    rw [Subgroup.index_prod, AddSubgroup.index_toSubgroup, Int.index_zmultiples]
    exact mul_ne_zero (by simpa using hd0) (unitFiltration K n).index_ne_zero_of_finite
  have hle : P.comap (unitsEquivIntProd hϖ).toMonoidHom ≤ (normUnits K L).range := by
    intro x hx
    simp only [Subgroup.mem_comap, Subgroup.mem_prod, MulEquiv.coe_toMonoidHom, P] at hx
    obtain ⟨h1, h2⟩ := hx
    set p := unitsEquivIntProd hϖ x with hp
    have hxp : x = unitsOfIntProd hϖ (p.1, p.2) := by
      rw [← unitsEquivIntProd_symm_apply, Prod.mk.eta, hp, MulEquiv.symm_apply_apply]
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp ((Multiplicative.mem_toSubgroup _ _).mp h1)
    rw [hxp, unitsOfIntProd_eq, ← hj, smul_eq_mul, mul_comm j, zpow_mul, zpow_natCast]
    refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ (MonoidHom.mem_range.mpr ⟨Units.map
      (algebraMap K L : K →* L) (uniformizerUnit hϖ), ?_⟩) _) (hn (Subgroup.mem_map.mpr ⟨_, h2, rfl⟩))
    ext
    simp [Algebra.norm_algebraMap, hd]
  have : (P.comap (unitsEquivIntProd hϖ).toMonoidHom).FiniteIndex := by
    constructor
    rw [Subgroup.index_comap_of_surjective _ (unitsEquivIntProd hϖ).surjective]
    exact hP
  exact Subgroup.finiteIndex_of_le hle

end Separable

end Local

end GroundTheory.LocalField
