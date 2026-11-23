import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibInfEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem um_eq_smul_of_sigmaCompact [SigmaCompactSpace G] (μ' μ : Measure G) [IsHaarMeasure μ]
    [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    μ' = haarScalarFactor μ' μ • μ := by
  refine (Measure.ext_iff_of_iUnion_eq_univ (iUnion_compactCovering G)).2 fun n => ?_
  ext t ht
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht, Measure.smul_apply]
  exact measure_isMulInvariant_eq_smul_of_isCompact_closure μ' μ
    ((isCompact_compactCovering G n).closure_of_subset Set.inter_subset_right)

def umD (Γ H : Subgroup G) (x : G) : Set G := {y | ∃ γ ∈ Γ, ∃ h ∈ H, y = γ * x * h}

theorem um_self_mem_D (Γ H : Subgroup G) (x : G) : x ∈ umD Γ H x := by
  simp only [umD, Set.mem_setOf_eq]
  exact ⟨1, Γ.one_mem, 1, H.one_mem, by simp⟩

theorem um_D_subset (Γ H : Subgroup G) {x z : G} (hz : z ∈ umD Γ H x) :
    umD Γ H z ⊆ umD Γ H x := by
  simp only [umD, Set.subset_def, Set.mem_setOf_eq] at hz ⊢
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hz
  rintro y ⟨γ', hγ', h', hh', rfl⟩
  exact ⟨γ' * γ, Γ.mul_mem hγ' hγ, h * h', H.mul_mem hh hh', by simp only [mul_assoc]⟩

theorem um_D_eq (Γ H : Subgroup G) {x z : G} (hz : z ∈ umD Γ H x) : umD Γ H z = umD Γ H x := by
  apply Set.Subset.antisymm (um_D_subset Γ H hz)
  apply um_D_subset Γ H
  simp only [umD, Set.mem_setOf_eq] at hz ⊢
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hz
  exact ⟨γ⁻¹, Γ.inv_mem hγ, h⁻¹, H.inv_mem hh, by group⟩

theorem um_D_open (Γ H : Subgroup G) (hH : IsOpen (H : Set G)) (x : G) :
    IsOpen (umD Γ H x) := by
  have e : umD Γ H x = ⋃ γ ∈ Γ, (fun h => γ * x * h) '' (H : Set G) := by
    ext y
    simp only [umD, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨γ, hγ, h, hh, rfl⟩
      exact ⟨γ, hγ, h, hh, rfl⟩
    · rintro ⟨γ, hγ, h, hh, rfl⟩
      exact ⟨γ, hγ, h, hh, rfl⟩
  rw [e]
  exact isOpen_biUnion fun γ _ => isOpenMap_mul_left (γ * x) _ hH

theorem um_D_smul (Γ H : Subgroup G) (x : G) (γ : Γ) : γ • umD Γ H x = umD Γ H x := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [umD, Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv]
  constructor
  · rintro ⟨δ, hδ, h, hh, e⟩
    refine ⟨(γ : G) * δ, Γ.mul_mem γ.2 hδ, h, hh, ?_⟩
    have e2 : y = (γ : G) * ((γ : G)⁻¹ * y) := by group
    rw [e2, e]
    simp only [mul_assoc]
  · rintro ⟨δ, hδ, h, hh, rfl⟩
    exact ⟨(γ : G)⁻¹ * δ, Γ.mul_mem (Γ.inv_mem γ.2) hδ, h, hh, by simp only [mul_assoc, inv_mul_cancel_left]⟩

theorem um_smulInv (Γ : Subgroup G) (μ : Measure G) [IsMulLeftInvariant μ] :
    SMulInvariantMeasure Γ G μ := inferInstance

theorem um_sigmaCompact (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [IsHaarMeasure μ]
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 < ⊤) : SigmaCompactSpace G := by
  have := um_smulInv Γ μ
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set W : Set G := V ∪ V⁻¹ with hWdef
  have hWc : IsCompact W := hVc.union hVc.inv
  have hWinv : W⁻¹ = W := by rw [hWdef, Set.union_inv, inv_inv, union_comm]
  set H : Subgroup G := Subgroup.closure V with hHdef
  have hHo : IsOpen (H : Set G) :=
    Subgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset hV1 Subgroup.subset_closure)
  have hPc : ∀ n : ℕ, IsCompact (W ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact isCompact_singleton
    | succ n ih => rw [pow_succ]; exact ih.mul hWc
  have hHc : (H : Set G) ⊆ ⋃ n : ℕ, W ^ n := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact mem_iUnion.2 ⟨1, by rw [pow_one]; exact Or.inl hx⟩
    | one => exact mem_iUnion.2 ⟨0, by rw [pow_zero]; exact Set.mem_one.2 rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨m, hm⟩ := mem_iUnion.1 hx
      obtain ⟨n, hn⟩ := mem_iUnion.1 hy
      exact mem_iUnion.2 ⟨m + n, by rw [pow_add]; exact Set.mul_mem_mul hm hn⟩
    | inv x _ hx =>
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      refine mem_iUnion.2 ⟨n, ?_⟩
      have h' : (W ^ n)⁻¹ = W ^ n := by rw [← inv_pow, hWinv]
      rw [← h']
      exact Set.inv_mem_inv.2 hn
  let ι := ↥(range (umD Γ H))
  have hpos : ∀ d : ι, 0 < μ ((d : Set G) ∩ 𝓕) := by
    rintro ⟨d, x, rfl⟩
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have h1 := h𝓕.measure_zero_of_invariant (umD Γ H x) (um_D_smul Γ H x) h0
    exact (um_D_open Γ H hHo x).measure_ne_zero μ ⟨x, um_self_mem_D Γ H x⟩ h1
  have hdisj : Pairwise (Disjoint on fun d : ι => (d : Set G) ∩ 𝓕) := by
    rintro ⟨d, x, rfl⟩ ⟨d', x', rfl⟩ hne
    refine Disjoint.mono inter_subset_left inter_subset_left ?_
    refine Set.disjoint_left.2 fun z hz hz' => hne ?_
    exact Subtype.ext ((um_D_eq Γ H hz).symm.trans (um_D_eq Γ H hz'))
  have hctbl : Countable ι := by
    have := Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ μ
      (As := fun d : ι => (d : Set G) ∩ 𝓕)
      (fun d => by
        rcases d with ⟨_, x, rfl⟩
        exact (um_D_open Γ H hHo x).measurableSet.nullMeasurableSet.inter h𝓕.nullMeasurableSet)
      hdisj.aedisjoint
      (ne_top_of_le_ne_top hfin.ne (measure_mono (iUnion_subset fun _ => inter_subset_right)))
    have hall : {d : ι | 0 < μ ((d : Set G) ∩ 𝓕)} = univ := eq_univ_of_forall hpos
    rw [hall] at this
    exact countable_univ_iff.1 this
  let rep : ι → G := fun d => d.2.choose
  have hrep : ∀ d : ι, umD Γ H (rep d) = d := fun d => d.2.choose_spec
  let K : ι × Γ × ℕ → Set G := fun p => (fun z => (p.2.1 : G) * rep p.1 * z) '' (W ^ p.2.2)
  have hK : ∀ p, IsCompact (K p) := fun p => (hPc p.2.2).image (by fun_prop)
  have hcov : (⋃ p, K p) = univ := by
    refine eq_univ_of_forall fun y => ?_
    let d : ι := ⟨umD Γ H y, y, rfl⟩
    have hy : y ∈ umD Γ H (rep d) := by rw [hrep d]; exact um_self_mem_D Γ H y
    obtain ⟨γ, hγ, h, hh, hyeq⟩ := hy
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hHc hh)
    exact mem_iUnion.2 ⟨(d, ⟨γ, hγ⟩, n), h, hn, hyeq.symm⟩
  rw [← isSigmaCompact_univ_iff, ← hcov]
  exact isSigmaCompact_iUnion_of_isCompact K hK

theorem um_rightInv (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [IsHaarMeasure μ]
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 < ⊤) : IsMulRightInvariant μ := by
  haveI := um_sigmaCompact Γ μ 𝓕 h𝓕 hfin
  haveI : SMulInvariantMeasure Γ G μ := um_smulInv Γ μ
  refine ⟨fun g => ?_⟩
  haveI : IsMulLeftInvariant (map (· * g) μ) := inferInstance
  haveI : IsFiniteMeasureOnCompacts (map (· * g) μ) := by
    refine ⟨fun K hK => ?_⟩
    rw [map_apply (measurable_mul_const g) hK.measurableSet]
    exact ((Homeomorph.mulRight g).isCompact_preimage.2 hK).measure_lt_top
  have hc := um_eq_smul_of_sigmaCompact (map (· * g) μ) μ
  have h𝓕' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv ⟨measurable_mul_const g, by rw [hc]; exact Measure.smul_absolutelyContinuous⟩
      Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have heq : μ ((· * g) ⁻¹' 𝓕) = μ 𝓕 := h𝓕'.measure_eq h𝓕
  have h1 := (MeasurableEquiv.mulRight g).map_apply (μ := μ) 𝓕
  simp only [MeasurableEquiv.coe_mulRight] at h1
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have e := congrArg (fun ν : Measure G => ν 𝓕) hc
  simp only [h1, heq, Measure.nnreal_smul_coe_apply] at e
  have hc1 : haarScalarFactor (map (· * g) μ) μ = 1 := by
    have e2 := (ENNReal.mul_left_inj hne hfin.ne).1 (e.symm.trans (one_mul _).symm)
    exact ENNReal.coe_eq_one.1 e2
  rw [hc, hc1, one_smul]

end Gen

section Spec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct

theorem um_countable_HFinIn (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    Countable (HFinIn (AF F) σ J) := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  have : Countable (GL (Fin M) E) :=
    Function.Injective.countable (f := fun u : GL (Fin M) E => (u : Matrix (Fin M) (Fin M) E))
      (fun _ _ h => Units.ext h)
  have hx : ∀ x : HFinIn (AF F) σ J, ∃ u : GL (Fin M) E,
      Formalism.UG.bc (inclR (AF F)) u = ((x : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) := by
    intro x
    have h : ((x : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) ∈ HFin (AF F) σ J :=
      Subgroup.mem_subgroupOf.1 x.2
    unfold HFin at h
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 h
    exact ⟨u, hu⟩
  refine Function.Injective.countable (f := fun x => (hx x).choose) ?_
  intro x y hxy
  have h1 := (hx x).choose_spec
  have h2 := (hx y).choose_spec
  simp only at hxy
  rw [hxy] at h1
  exact Subtype.ext (Subtype.ext (h1.symm.trans h2))

instance t2Space_adelic_unitary (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    T2Space (HA (AF F) σ J) := inferInstanceAs (T2Space (HR (AF F) σ J))

theorem um_sigmaCompact_HA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (h : SWa1 F E σ M J) : SigmaCompactSpace (HA (AF F) σ J) := by
  obtain ⟨μ, hμ⟩ := h.1
  have : μ.IsHaarMeasure := hμ
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := um_countable_HFinIn F E σ M J
  obtain ⟨𝓕, h𝓕⟩ := (h.2 μ hμ).1
  exact um_sigmaCompact Γ μ 𝓕 h𝓕 ((h.2 μ hμ).2 𝓕 h𝓕)

theorem unimod_holds : Unimod := by
  intro F E _ _ _ _ _ σ hσ M J _ hSWa1 _ _ _ _ _ _ _ μ hμ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : μ.IsHaarMeasure := hμ
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := um_countable_HFinIn F E σ M J
  obtain ⟨𝓕, h𝓕⟩ := (hSWa1.2 μ hμ).1
  exact um_rightInv Γ μ 𝓕 h𝓕 ((hSWa1.2 μ hμ).2 𝓕 h𝓕)

end Spec

end PI.VolStabSW
