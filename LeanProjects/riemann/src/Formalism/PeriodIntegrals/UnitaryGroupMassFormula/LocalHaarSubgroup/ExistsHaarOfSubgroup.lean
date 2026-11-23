import Mathlib

noncomputable section

open ValuativeRel MeasureTheory Topology Polynomial

namespace PI.LocHaarRRW

section General

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V]

theorem exists_haar_of_subgroup [SigmaCompactSpace V] (R : AddSubgroup V)
    (h0 : (R : Set V) ∈ 𝓝 (0 : V)) {C : Set V} (hC : IsCompact C) (hRC : (R : Set V) ⊆ C) :
    ∃ μ : Measure V, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ μ (R : Set V) = 1 := by
  have hRo : IsOpen (R : Set V) := AddSubgroup.isOpen_of_mem_nhds R h0
  have hRc : IsClosed (R : Set V) := R.isClosed_of_isOpen hRo
  have hRk : IsCompact (R : Set V) := hC.of_isClosed_subset hRc hRC
  let K0 : TopologicalSpace.PositiveCompacts V :=
    { carrier := R, isCompact' := hRk,
      interior_nonempty' := by rw [hRo.interior_eq]; exact ⟨0, R.zero_mem⟩ }
  refine ⟨Measure.addHaarMeasure K0, inferInstance, inferInstance, ?_⟩
  exact Measure.addHaarMeasure_self

end General

section Field

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem isCompact_integer : IsCompact (𝒪[K] : Set K) :=
  isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[K])

theorem isOpen_integer' : IsOpen (𝒪[K] : Set K) := Valuation.isOpen_integer

variable {K} in
theorem inv_mem_integer {x : K} (hx : x ∉ 𝒪[K]) : x⁻¹ ∈ 𝒪[K] := by
  rw [Valuation.mem_integer_iff] at hx ⊢
  rw [map_inv₀]
  push Not at hx
  exact inv_le_one_of_one_le₀ hx.le

theorem sigmaCompactSpace_lf : SigmaCompactSpace K := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨⟨fun n => (fun y : K => ((ϖ : K) ^ n)⁻¹ * y) '' (𝒪[K] : Set K),
    fun n => (isCompact_integer K).image (continuous_const.mul continuous_id), ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  rw [Set.mem_iUnion]
  by_cases hx : x ∈ 𝒪[K]
  · exact ⟨0, x, hx, by simp⟩
  · have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
    have hxi : x⁻¹ ∈ 𝒪[K] := inv_mem_integer hx
    have hne : (⟨x⁻¹, hxi⟩ : 𝒪[K]) ≠ 0 := by
      intro h
      apply hx0
      have := congrArg (fun z : 𝒪[K] => (z : K)) h
      simpa using this
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
    have h1 : x⁻¹ = (u : K) * (ϖ : K) ^ n := by
      have := congrArg (fun z : 𝒪[K] => (z : K)) hu
      simpa using this
    set y : K := (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) : K) with hy
    have h2 : (u : K) * y = 1 := by
      rw [hy]; exact congrArg Subtype.val u.mul_inv
    have hp : ((ϖ : K) ^ n) ≠ 0 := pow_ne_zero _ hϖ0
    refine ⟨n, y, SetLike.coe_mem _, ?_⟩
    show ((ϖ : K) ^ n)⁻¹ * y = x
    have h3 : x⁻¹ * (((ϖ : K) ^ n)⁻¹ * y) = 1 := by
      rw [h1]
      calc (u : K) * (ϖ : K) ^ n * (((ϖ : K) ^ n)⁻¹ * y)
          = ((u : K) * y) * ((ϖ : K) ^ n * ((ϖ : K) ^ n)⁻¹) := by ring
        _ = 1 := by rw [h2, mul_inv_cancel₀ hp, one_mul]
    have h4 := inv_eq_of_mul_eq_one_right h3
    rw [inv_inv] at h4
    exact h4.symm

end Field

section Lin

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {M V : Type*} [AddCommGroup M] [Module K M] [TopologicalSpace M] [IsModuleTopology K M]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V]

def homeoOfLin (e : M ≃ₗ[K] V) : M ≃ₜ V :=
  haveI := IsModuleTopology.toContinuousAdd K V
  haveI := IsModuleTopology.toContinuousAdd K M
  { toEquiv := e.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

end Lin

section Alg

variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]

theorem memO_of_integral {y : K} (h : IsIntegral 𝒪[K] y) : y ∈ 𝒪[K] :=
  (Valuation.integer.integers _).mem_of_integral h

theorem integral_of_memO {y : K} (h : y ∈ 𝒪[K]) : IsIntegral 𝒪[K] y := by
  have : algebraMap 𝒪[K] K ⟨y, h⟩ = y := rfl
  exact this ▸ isIntegral_algebraMap

theorem memO_of_integral_V [Nontrivial V] {y : K} (h : IsIntegral 𝒪[K] (algebraMap K V y)) :
    y ∈ 𝒪[K] :=
  memO_of_integral ((isIntegral_algebraMap_iff (algebraMap K V).injective).1 h)

theorem integral_V_of_memO [Nontrivial V] {y : K} (h : y ∈ 𝒪[K]) :
    IsIntegral 𝒪[K] (algebraMap K V y) :=
  (isIntegral_algebraMap_iff (algebraMap K V).injective).2 (integral_of_memO h)

theorem pair_indep [Nontrivial V] {θ : V} (hθ : θ ∉ (algebraMap K V).range) (s t : K)
    (h : s • (1 : V) + t • θ = 0) : s = 0 ∧ t = 0 := by
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at h
    exact ⟨h, rfl⟩
  · exfalso
    apply hθ
    refine ⟨-(t⁻¹ * s), ?_⟩
    have h1 : t • θ = -(s • (1 : V)) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h)
    have h2 : θ = t⁻¹ • (t • θ) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, h1, smul_neg, smul_smul, ← neg_smul, Algebra.algebraMap_eq_smul_one]

theorem exists_sq [Module.Free K V] (hr : Module.finrank K V = 2) [IsReduced V] :
    ∃ θ : V, ∃ d : K, θ ∉ (algebraMap K V).range ∧ θ * θ = algebraMap K V d ∧ d ≠ 0 ∧
      d ∈ 𝒪[K] := by
  have hpos : 0 < Module.finrank K V := by rw [hr]; norm_num
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  haveI : Module.Finite K V := Module.finite_of_finrank_pos hpos
  set ι := algebraMap K V with hι
  obtain ⟨θ0, hθ0⟩ : ∃ θ0 : V, θ0 ∉ ι.range := by
    by_contra hall
    push Not at hall
    have htop : (⊤ : Submodule K V) = Submodule.span K {1} := by
      ext x
      simp only [Submodule.mem_top, true_iff, Submodule.mem_span_singleton]
      obtain ⟨c, rfl⟩ := hall x
      exact ⟨c, (Algebra.algebraMap_eq_smul_one c).symm⟩
    have h1 := finrank_span_singleton (K := K) (one_ne_zero : (1 : V) ≠ 0)
    rw [← htop, finrank_top, hr] at h1
    norm_num at h1
  have hli : LinearIndependent K ![(1 : V), θ0] :=
    LinearIndependent.pair_iff.mpr (pair_indep hθ0)
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = θ0 := by simp [b]
  have hb := b.sum_repr (θ0 * θ0)
  rw [Fin.sum_univ_two, hb0, hb1] at hb
  set α := b.repr (θ0 * θ0) 0
  set β := b.repr (θ0 * θ0) 1
  have hsq : θ0 * θ0 = ι α + ι β * θ0 := by
    rw [← hb, Algebra.smul_def, Algebra.smul_def, mul_one]
  have h2 : ι β = 2 * ι (β / 2) := by
    rw [← map_ofNat ι 2, ← map_mul]; congr 1; field_simp
  set θ1 := θ0 - ι (β / 2) with hθ1def
  have hθ1 : θ1 * θ1 = ι (α + (β / 2) ^ 2) := by
    rw [hθ1def, map_add, map_pow]
    linear_combination hsq + θ0 * h2
  have hθ1r : θ1 ∉ ι.range := by
    rintro ⟨c, hc⟩
    apply hθ0
    refine ⟨c + β / 2, ?_⟩
    rw [map_add, hc, hθ1def]; ring
  have hd1 : α + (β / 2) ^ 2 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hθ1
    have hn : IsNilpotent θ1 := ⟨2, by rw [pow_two]; exact hθ1⟩
    apply hθ1r
    exact ⟨0, by rw [map_zero, IsReduced.eq_zero θ1 hn]⟩
  set d1 := α + (β / 2) ^ 2
  by_cases hdO : d1 ∈ 𝒪[K]
  · exact ⟨θ1, d1, hθ1r, hθ1, hd1, hdO⟩
  · refine ⟨ι d1⁻¹ * θ1, d1⁻¹, ?_, ?_, inv_ne_zero hd1, inv_mem_integer hdO⟩
    · rintro ⟨c, hc⟩
      apply hθ1r
      refine ⟨d1 * c, ?_⟩
      rw [map_mul, hc, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hd1, map_one, one_mul]
    · calc ι d1⁻¹ * θ1 * (ι d1⁻¹ * θ1) = ι d1⁻¹ * ι d1⁻¹ * (θ1 * θ1) := by ring
        _ = ι d1⁻¹ := by
          rw [hθ1, ← map_mul, ← map_mul]; congr 1; field_simp

end Alg

end PI.LocHaarRRW
