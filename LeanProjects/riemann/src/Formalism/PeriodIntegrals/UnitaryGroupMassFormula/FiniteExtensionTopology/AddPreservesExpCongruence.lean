import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteExtensionTopology.Imports

noncomputable section

namespace PI.UnitaryGroupMassFormula.FinExtTop

open PI.FinExtTop Topology Filter

section

variable {O' : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']

def fracB (ϖ : O') (i : ℕ) : Submodule O' (FractionRing O') :=
  Submodule.span O' {algebraMap O' (FractionRing O') (ϖ ^ i)}

theorem mem_fracB {ϖ : O'} {i : ℕ} {x : FractionRing O'} :
    x ∈ fracB ϖ i ↔ ∃ c : O', x = algebraMap O' (FractionRing O') (c * ϖ ^ i) := by
  simp only [fracB, Submodule.mem_span_singleton]
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
    exact ⟨c, by rw [mul_comm]; exact IsFractionRing.injective O' (FractionRing O') hc⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [mul_comm]⟩

theorem fracB_anti (ϖ : O') {i j : ℕ} (h : i ≤ j) : fracB ϖ j ≤ fracB ϖ i := by
  intro x hx
  rw [mem_fracB] at hx ⊢
  obtain ⟨c, rfl⟩ := hx
  exact ⟨c * ϖ ^ (j - i), by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]⟩

theorem exists_pow_mul_mem {ϖ : O'} (hϖ : Irreducible ϖ) (a : FractionRing O') :
    ∃ n : ℕ, ∃ c : O', algebraMap O' (FractionRing O') (ϖ ^ n) * a =
      algebraMap O' (FractionRing O') c := by
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors O') a
  have hy : (y : O') ≠ 0 := nonZeroDivisors.ne_zero y.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  refine ⟨n, x * ↑u⁻¹, ?_⟩
  have hy' : algebraMap O' (FractionRing O') (y : O') =
      algebraMap O' (FractionRing O') (↑u) * algebraMap O' (FractionRing O') (ϖ ^ n) := by
    rw [hu, map_mul]
  have hu1 : algebraMap O' (FractionRing O') (↑u) * algebraMap O' (FractionRing O') (↑u⁻¹) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hxy' : a * algebraMap O' (FractionRing O') (y : O') = algebraMap O' (FractionRing O') x := hxy
  rw [map_mul, ← hxy']
  linear_combination (-(a * algebraMap O' (FractionRing O') (↑u⁻¹))) * hy' +
    (-(algebraMap O' (FractionRing O') (ϖ ^ n) * a)) * hu1

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

end

theorem addPreservesExpCongruence : S3 := by
  unfold S3
  intro O' _ _ _ _ hadic
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O'
  letI : TopologicalSpace (FractionRing O') := (fracB_basis hϖ).topology
  have hring : IsTopologicalRing (FractionRing O') := by
    first
    | exact (fracB_basis hϖ).toRingFilterBasis.isTopologicalRing
    | exact @RingFilterBasis.isTopologicalRing _ _ (fracB_basis hϖ).toRingFilterBasis
    | infer_instance
  have hadd : IsTopologicalAddGroup (FractionRing O') := by
    first
    | exact hring.toIsTopologicalAddGroup
    | exact @IsTopologicalRing.toIsTopologicalAddGroup _ _ _ hring
    | infer_instance
  have hnhds : (nhds (0 : FractionRing O')).HasBasis (fun _ : ℕ => True)
      (fun i => (fracB ϖ i : Set (FractionRing O'))) := by
    first
    | exact (fracB_basis hϖ).toRing_subgroups_basis.hasBasis_nhds_zero
    | exact (fracB_basis hϖ).toRingSubgroupsBasis.hasBasis_nhds_zero
    | exact (fracB_basis hϖ).toRing_subgroups_basis.hasBasis_nhds_zero'
  have hringO : IsTopologicalRing O' := by
    have h' : ‹TopologicalSpace O'› = (IsLocalRing.maximalIdeal O').adicTopology := hadic
    rw [h']
    first
    | exact (IsLocalRing.maximalIdeal O').adic_basis.toRingFilterBasis.isTopologicalRing
    | infer_instance
  have hm : IsLocalRing.maximalIdeal O' = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hpow : ∀ i : ℕ, ((IsLocalRing.maximalIdeal O' ^ i : Ideal O') : Set O') = {x | ϖ ^ i ∣ x} := by
    intro i
    ext x
    simp only [hm, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton,
      Set.mem_setOf_eq]
  have hadic' := isAdic_iff.1 hadic
  have hnhdsO : (nhds (0 : O')).HasBasis (fun _ : ℕ => True) (fun i => {x : O' | ϖ ^ i ∣ x}) := by
    refine ⟨fun s => ⟨fun hs => ?_, fun ⟨i, _, hi⟩ => ?_⟩⟩
    · obtain ⟨i, hi⟩ := hadic'.2 s hs
      exact ⟨i, trivial, by rw [← hpow]; exact hi⟩
    · refine Filter.mem_of_superset ((hadic'.1 i).mem_nhds ?_) (by rw [hpow]; exact hi)
      exact zero_mem _
  have hpre : ∀ i : ℕ, algebraMap O' (FractionRing O') ⁻¹' (fracB ϖ i : Set (FractionRing O')) =
      {x : O' | ϖ ^ i ∣ x} := by
    intro i
    ext x
    exact algebraMap_mem_fracB
  haveI := hring
  haveI := hringO
  have h0 : nhds (0 : O') = Filter.comap (algebraMap O' (FractionRing O')) (nhds 0) := by
    refine hnhdsO.eq_of_same_basis ?_
    have h2 := hnhds.comap (algebraMap O' (FractionRing O'))
    simp only [hpre] at h2
    exact h2
  have hind : Topology.IsInducing (algebraMap O' (FractionRing O')) := by
    refine Topology.isInducing_iff_nhds.2 fun x => ?_
    rw [← nhds_translation_add_neg x, ← nhds_translation_add_neg (algebraMap O' (FractionRing O') x),
      h0, Filter.comap_comap, Filter.comap_comap]
    congr 1
    funext y
    simp only [Function.comp, map_add, map_neg]
  have hcont : Continuous (algebraMap O' (FractionRing O')) := hind.continuous
  have hrange : Set.range (algebraMap O' (FractionRing O')) = (fracB ϖ 0 : Set (FractionRing O')) := by
    ext x
    simp only [Set.mem_range, SetLike.mem_coe, mem_fracB, pow_zero, mul_one]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
  have hopen : IsOpen (fracB ϖ 0 : Set (FractionRing O')) :=
    (fracB ϖ 0).toAddSubgroup.isOpen_of_mem_nhds (hnhds.mem_of_mem trivial)
  refine ⟨inferInstance, hadd, continuousSMul_of_algebraMap O' (FractionRing O') hcont, ?_⟩
  first
  | exact ⟨⟨hind, IsFractionRing.injective O' (FractionRing O')⟩, by rw [hrange]; exact hopen⟩
  | (show Topology.IsOpenEmbedding _
     exact ⟨⟨hind, IsFractionRing.injective O' (FractionRing O')⟩, by rw [hrange]; exact hopen⟩)

end PI.UnitaryGroupMassFormula.FinExtTop
