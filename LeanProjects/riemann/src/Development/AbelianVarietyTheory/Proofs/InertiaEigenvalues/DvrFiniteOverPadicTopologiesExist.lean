import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

noncomputable section

namespace GlobalTheory.PadicTop

open IsLocalRing Topology
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop TopEx)

theorem padicCoeff_of_finite {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] [TopologicalSpace O]
    [IsModuleTopology ℤ_[p] O] (hinj : Function.Injective (algebraMap ℤ_[p] O)) : PadicCoeff p O := by
  haveI : Module.IsTorsionFree ℤ_[p] O := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.Free ℤ_[p] O := inferInstance
  haveI hR : IsTopologicalRing O := IsModuleTopology.isTopologicalRing ℤ_[p] O
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set b := Module.Free.chooseBasis ℤ_[p] O
  set e : O ≃ₗ[ℤ_[p]] (Module.Free.ChooseBasisIndex ℤ_[p] O → ℤ_[p]) := b.equivFun with he_def
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : O ≃ₜ (Module.Free.ChooseBasisIndex ℤ_[p] O → ℤ_[p]) :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  have hp0 : (p : O) ≠ 0 := by
    rw [← map_natCast (algebraMap ℤ_[p] O), Ne, ← map_zero (algebraMap ℤ_[p] O), hinj.eq_iff]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpm : (p : O) ∈ maximalIdeal O := by
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ_[p]) (maximalIdeal O)
    have hc : (maximalIdeal O).comap (algebraMap ℤ_[p] O) = maximalIdeal ℤ_[p] :=
      IsLocalRing.eq_maximalIdeal hmax
    rw [← map_natCast (algebraMap ℤ_[p] O), ← Ideal.mem_comap, hc, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  have key1 : ∀ (n : ℕ) (x : O), ‖e x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) → x ∈ Ideal.span {(p : O) ^ n} := by
    intro n x hx
    have hc : ∀ i, e x i ∈ Ideal.span {(p : ℤ_[p]) ^ n} := fun i =>
      (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 ((norm_le_pi_norm (e x) i).trans hx)
    choose c hc using fun i => Ideal.mem_span_singleton'.1 (hc i)
    rw [Ideal.mem_span_singleton']
    refine ⟨∑ i, c i • b i, ?_⟩
    have hx' : x = ∑ i, e x i • b i := (b.sum_equivFun x).symm
    conv_rhs => rw [hx']
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i]
    simp only [Algebra.smul_def, map_mul, map_pow, map_natCast]
    ring
  have key2 : ∀ (n : ℕ) (x : O), x ∈ Ideal.span {(p : O) ^ n} → ‖e x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
    intro n x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have hy : y * (p : O) ^ n = ((p : ℤ_[p]) ^ n) • y := by
      rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]
    refine (pi_norm_le_iff_of_nonneg (zpow_pos hpR _).le).2 fun i => ?_
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, hy, map_smul, Pi.smul_apply, smul_eq_mul]
    exact Ideal.mem_span_singleton'.2 ⟨e y i, mul_comm _ _⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hsub1 : ∀ n : ℕ, Ideal.span {(p : O) ^ n} ≤ maximalIdeal O ^ n := fun n =>
    Ideal.span_le.2 (Set.singleton_subset_iff.2 (Ideal.pow_mem_pow hpm n))
  have hsub2 : ∀ n : ℕ, maximalIdeal O ^ (k * n) ≤ Ideal.span {(p : O) ^ n} := by
    intro n
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    have hk : ϖ ^ k = ↑u⁻¹ * (p : O) := by rw [hu, Units.inv_mul_cancel_left]
    rw [pow_mul, hk, mul_pow]
    exact Dvd.intro_left _ rfl
  refine ⟨hR, h.symm.compactSpace, h.symm.t2Space, ?_, hpm, hp0⟩
  refine isAdic_iff.2 ⟨fun n => ?_, fun s hs => ?_⟩
  · have hn : e ⁻¹' Metric.closedBall 0 ((p : ℝ) ^ (-(n : ℤ))) ∈ 𝓝 (0 : O) :=
      he.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact Metric.closedBall_mem_nhds 0 (zpow_pos hpR _))
    refine AddSubgroup.isOpen_of_mem_nhds (maximalIdeal O ^ n).toAddSubgroup (g := 0)
      (Filter.mem_of_superset hn fun x hx => hsub1 n (key1 n x ?_))
    simpa using hx
  · have ht : e.symm ⁻¹' s ∈ 𝓝 (0 : Module.Free.ChooseBasisIndex ℤ_[p] O → ℤ_[p]) :=
      he'.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hs)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ht
    have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp1
    refine ⟨k * n, fun x hx => ?_⟩
    have h1 := key2 n x (hsub2 n hx)
    have h2 : e x ∈ Metric.ball 0 ε := by
      rw [Metric.mem_ball, dist_zero_right]
      refine lt_of_le_of_lt h1 ?_
      rwa [zpow_neg, zpow_natCast, ← inv_pow]
    have := hball h2
    simpa using this

section FracTopology

variable {O' : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']

def fracB (ϖ : O') (i : ℕ) : Submodule O' (FractionRing O') :=
  Submodule.span O' {algebraMap O' (FractionRing O') (ϖ ^ i)}

theorem mem_fracB {ϖ : O'} {i : ℕ} {x : FractionRing O'} :
    x ∈ fracB ϖ i ↔ ∃ c : O', x = algebraMap O' (FractionRing O') (c * ϖ ^ i) := by
  rw [fracB, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Algebra.smul_def, map_mul]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Algebra.smul_def, map_mul]⟩

theorem algebraMap_mem_fracB {ϖ : O'} {i : ℕ} {x : O'} :
    algebraMap O' (FractionRing O') x ∈ fracB ϖ i ↔ ϖ ^ i ∣ x := by
  rw [mem_fracB]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [IsFractionRing.injective O' (FractionRing O') hc, mul_comm]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [mul_comm]⟩

theorem fracB_anti (ϖ : O') {i j : ℕ} (h : i ≤ j) : fracB ϖ j ≤ fracB ϖ i := by
  rw [fracB, Submodule.span_singleton_le_iff_mem, algebraMap_mem_fracB]
  exact pow_dvd_pow ϖ h

theorem exists_pow_mul_mem {ϖ : O'} (hϖ : Irreducible ϖ) (a : FractionRing O') :
    ∃ n : ℕ, ∃ c : O', algebraMap O' (FractionRing O') (ϖ ^ n) * a =
      algebraMap O' (FractionRing O') c := by
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors O') a
  have hs : (s : O') ≠ 0 := nonZeroDivisors.ne_zero s.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
  refine ⟨n, ↑u⁻¹ * r, ?_⟩
  have hn : ϖ ^ n = ↑u⁻¹ * (s : O') := by rw [hu, Units.inv_mul_cancel_left]
  rw [hn, map_mul, map_mul, mul_assoc, mul_comm (algebraMap O' (FractionRing O') (s : O')) a]
  exact congrArg _ h

theorem fracB_basis {ϖ : O'} (hϖ : Irreducible ϖ) : SubmodulesRingBasis (fracB ϖ) where
  inter i j := ⟨max i j, le_inf (fracB_anti ϖ (le_max_left _ _)) (fracB_anti ϖ (le_max_right _ _))⟩
  leftMul a i := by
    obtain ⟨n, c, hc⟩ := exists_pow_mul_mem hϖ a
    refine ⟨i + n, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨d, rfl⟩ := mem_fracB.1 hx
    refine mem_fracB.2 ⟨c * d, ?_⟩
    have e : algebraMap O' (FractionRing O') (d * ϖ ^ (i + n)) =
        algebraMap O' (FractionRing O') (d * ϖ ^ i) * algebraMap O' (FractionRing O') (ϖ ^ n) := by
      rw [← map_mul, pow_add, mul_assoc]
    show a * _ = _
    rw [e, mul_comm (algebraMap O' (FractionRing O') (d * ϖ ^ i)), ← mul_assoc, mul_comm a, hc,
      ← map_mul]
    congr 1
    ring
  mul i := ⟨i, by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_fracB.1 hx
    obtain ⟨d, rfl⟩ := mem_fracB.1 hy
    exact mem_fracB.2 ⟨c * d * ϖ ^ i, by show _ * _ = _; rw [← map_mul]; congr 1; ring⟩⟩

end FracTopology

theorem exists_fracTop (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [TopologicalSpace O'] (hA : IsAdic (IsLocalRing.maximalIdeal O')) :
    ∃ (_ : TopologicalSpace (FractionRing O')) (_ : IsTopologicalAddGroup (FractionRing O'))
      (_ : ContinuousSMul O' (FractionRing O')), FracTop O' := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hm : ∀ n : ℕ, ((IsLocalRing.maximalIdeal O' ^ n : Ideal O') : Set O') = {x | ϖ ^ n ∣ x} := by
    intro n
    ext x
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
      SetLike.mem_coe, Ideal.mem_span_singleton]
    rfl
  have hB := fracB_basis hϖ
  have hR := hB.toRing_subgroups_basis
  let τK : TopologicalSpace (FractionRing O') := hB.topology
  have hTR : IsTopologicalRing (FractionRing O') := hR.toRingFilterBasis.isTopologicalRing
  set f := algebraMap O' (FractionRing O') with hf
  have hnK := hR.hasBasis_nhds
  have hnO := hA.hasBasis_nhds
  have hcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    refine ((hnO x).tendsto_iff (hnK (f x))).2 fun i _ => ⟨i, trivial, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hm] at hz
    show f (x + z) - f x ∈ fracB ϖ i
    rw [map_add, add_sub_cancel_left]
    exact algebraMap_mem_fracB.2 hz
  have hopen : IsOpenMap f := by
    refine IsOpenMap.of_nhds_le fun x => ?_
    refine Filter.le_map fun s hs => ?_
    obtain ⟨n, -, hn⟩ := (hnO x).mem_iff.1 hs
    refine Filter.mem_of_superset ((hnK (f x)).mem_of_mem (i := n) trivial) ?_
    intro b hb
    obtain ⟨c, hc⟩ := mem_fracB.1 (show b - f x ∈ fracB ϖ n from hb)
    refine ⟨x + c * ϖ ^ n, hn ⟨c * ϖ ^ n, ?_, rfl⟩, ?_⟩
    · rw [hm]
      exact Dvd.intro_left c rfl
    · rw [map_add, ← hc, add_sub_cancel]
  refine ⟨τK, inferInstance, continuousSMul_of_algebraMap O' (FractionRing O') hcont, ⟨?_⟩⟩
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont
    (IsFractionRing.injective O' (FractionRing O')) hopen

theorem topEx : TopEx := by
  intro p _ O _ _ _ _ _ hinj
  letI τ : TopologicalSpace O := moduleTopology ℤ_[p] O
  haveI : IsModuleTopology ℤ_[p] O := ⟨rfl⟩
  have hO := padicCoeff_of_finite hinj
  obtain ⟨τK, h1, h2, h3⟩ := exists_fracTop O hO.adic
  exact ⟨τ, τK, h1, h2, hO, h3⟩

end GlobalTheory.PadicTop
