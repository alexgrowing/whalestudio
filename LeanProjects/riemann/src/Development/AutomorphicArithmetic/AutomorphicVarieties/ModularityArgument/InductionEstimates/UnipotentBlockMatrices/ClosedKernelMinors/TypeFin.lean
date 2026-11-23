import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [T2Space G]

private theorem integ {U : Set G} (hU : IsCompact U) {ν : Measure G} [IsProbabilityMeasure ν] (hs : ∀ᵐ k ∂ν, k ∈ U)
    {F : G → ℂ} (hF : Continuous F) : Integrable F ν := by
  have h := hF.continuousOn.integrableOn_compact (μ := ν) hU
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] at h

private def fixSub {U : Set G} (hU : IsCompact U) (ν : Measure G) [IsProbabilityMeasure ν] (hs : ∀ᵐ k ∂ν, k ∈ U)
    {e : G → ℂ} (he : Continuous e) : Submodule ℂ (G → ℂ) where
  carrier := {F | Continuous F ∧ ∀ g, ∫ k, e k * F (g * k) ∂ν = F g}
  add_mem' := by
    rintro F F' ⟨hF, h⟩ ⟨hF', h'⟩
    refine ⟨hF.add hF', fun g => ?_⟩
    simp only [Pi.add_apply, mul_add]
    rw [integral_add (integ hU hs (by fun_prop)) (integ hU hs (by fun_prop)), h, h']
  zero_mem' := ⟨continuous_const, by simp⟩
  smul_mem' := by
    rintro c F ⟨hF, h⟩
    refine ⟨hF.const_smul c, fun g => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
    rw [integral_const_mul, h]

private theorem detect (U : Subgroup G) (hU : IsCompact (U : Set G)) (ν : Measure G) [IsProbabilityMeasure ν]
    (hs : ∀ᵐ k ∂ν, k ∈ U) (hinv : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) {e : G → ℂ} (he : Continuous e) :
    ∃ t : Finset G, (∀ x ∈ t, x ∈ U) ∧ ∀ F : G → ℂ, Continuous F → (∀ g, ∫ k, e k * F (g * k) ∂ν = F g) →
      (∀ x ∈ t, F x = 0) → ∀ x ∈ U, F x = 0 := by
  have h1 : ∀ u ∈ (U : Set G), {x : G | ∀ k ∈ (U : Set G), ‖e (x⁻¹ * k) - e (u⁻¹ * k)‖ < 1 / 2} ∈ 𝓝 u := by
    intro u _
    refine hU.eventually_forall_of_forall_eventually (x₀ := u)
      (P := fun x k => ‖e (x⁻¹ * k) - e (u⁻¹ * k)‖ < 1 / 2) fun k _ => ?_
    have hc : Continuous fun p : G × G => ‖e (p.1⁻¹ * p.2) - e (u⁻¹ * p.2)‖ := by fun_prop
    exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨t, ht, hcov⟩ := hU.elim_nhds_subcover _ h1
  refine ⟨t, ht, fun F hF hfix h0 => ?_⟩
  have hrep : ∀ u ∈ U, F u = ∫ k, e (u⁻¹ * k) * F k ∂ν := by
    intro u hu
    rw [← hfix u]
    conv_rhs => rw [← (hinv u hu).map_eq]
    rw [integral_map (hinv u hu).measurable.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    simp
  obtain ⟨x, hx, hmax⟩ := hU.exists_isMaxOn ⟨1, U.one_mem⟩ hF.norm.continuousOn
  have hx0 : ‖F x‖ ≤ 1 / 2 * ‖F x‖ := by
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 (hcov hx)
    have e1 : F x = ∫ k, (e (x⁻¹ * k) - e (u⁻¹ * k)) * F k ∂ν := by
      simp only [sub_mul]
      rw [integral_sub (integ hU hs (by fun_prop)) (integ hU hs (by fun_prop)), ← hrep x hx, ← hrep u (ht u hu), h0 u hu,
        sub_zero]
    have e2 := norm_integral_le_of_norm_le_const (μ := ν) (f := fun k => (e (x⁻¹ * k) - e (u⁻¹ * k)) * F k)
      (C := 1 / 2 * ‖F x‖) (by
        filter_upwards [hs] with k hk
        rw [norm_mul]
        exact mul_le_mul (hxu k hk).le (hmax hk) (norm_nonneg _) (by norm_num))
    rw [← e1] at e2
    simpa using e2
  intro y hy
  have : ‖F y‖ ≤ ‖F x‖ := hmax hy
  have := norm_nonneg (F x)
  exact norm_le_zero_iff.1 (by linarith)

end General

private theorem leftRight {H : Type} [Group H] (V : Submodule ℂ (H → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ a ∈ V, ∀ g, (fun x => a (g * x)) ∈ V) :
    FiniteDimensional ℂ (Submodule.span ℂ {b : H → ℂ | ∃ a ∈ V, ∃ u, b = fun x => a (x * u)}) := by
  classical
  let B := Module.finBasis ℂ V
  let L : H → V →ₗ[ℂ] V := fun g =>
    { toFun := fun a => ⟨fun x => (a : H → ℂ) (g * x), hV a a.2 g⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let c : Fin (Module.finrank ℂ V) × Fin (Module.finrank ℂ V) → H → ℂ := fun p x => B.repr (L x (B p.2)) p.1
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range c)) (Submodule.span_le.2 ?_)
  rintro _ ⟨a, ha, u, rfl⟩
  have key : (fun x => a (x * u)) = ∑ p : Fin (Module.finrank ℂ V) × Fin (Module.finrank ℂ V),
      (B.repr ⟨a, ha⟩ p.2 * (B p.1 : H → ℂ) u) • c p := by
    funext x
    have h1 : a (x * u) = (L x ⟨a, ha⟩ : H → ℂ) u := rfl
    have h2 : L x ⟨a, ha⟩ = ∑ i, ∑ j, (B.repr ⟨a, ha⟩ j * c (i, j) x) • B i := by
      conv_lhs => rw [← B.sum_repr ⟨a, ha⟩, map_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      conv_lhs => rw [← B.sum_repr (L x (B j))]
      rw [Finset.smul_sum]
      simp only [smul_smul, c]
    rw [h1, h2, Fintype.sum_prod_type]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [SetLike.mem_coe, key]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.typeFin :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n), IsCompact (D.U : Set (G1 K n)) ∧ D.U ≤ KG K n ∧ ∃ 𝒜 : Submodule ℂ (D.U → ℂ), FiniteDimensional ℂ 𝒜 ∧
      (∀ a ∈ 𝒜, Continuous a ∧ ∀ u : D.U, (fun x => a (x * u)) ∈ 𝒜) ∧
      ∀ f : G1 K n → ℂ, Continuous f → D.Fix f → ∀ g, (fun u : D.U => f (g * u)) ∈ 𝒜 := by
  intro K _ _ n D
  obtain ⟨O, hO, hUO⟩ := D.isOpen
  have hle : D.U ≤ KG K n := fun g hg => ((hUO g).1 hg).2
  have hK : IsCompact (KG K n : Set (G1 K n)) := ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 n).1
  have hU : IsCompact (D.U : Set (G1 K n)) := by
    haveI : CompactSpace (KG K n) := isCompact_iff_compactSpace.1 hK
    have hop : IsOpen ((D.U.subgroupOf (KG K n) : Subgroup (KG K n)) : Set (KG K n)) := by
      have : ((D.U.subgroupOf (KG K n) : Subgroup (KG K n)) : Set (KG K n)) =
          (fun k : KG K n => ((k : G1 K n) : AdelicGLn.AdelicGL K n)) ⁻¹' O := by
        ext k
        exact ⟨fun h => ((hUO k).1 h).1, fun h => (hUO k).2 ⟨h, k.2⟩⟩
      rw [this]
      exact hO.preimage (continuous_subtype_val.comp continuous_subtype_val)
    have := ((Subgroup.isClosed_of_isOpen _ hop).isCompact).image continuous_subtype_val
    convert this using 1
    ext g
    exact ⟨fun h => ⟨⟨g, hle h⟩, h, rfl⟩, by rintro ⟨k, hk, rfl⟩; exact hk⟩
  refine ⟨hU, hle, ?_⟩
  haveI := D.prob
  let V : Submodule ℂ (D.U → ℂ) := (fixSub hU D.ν D.supp D.cont).map (LinearMap.funLeft ℂ ℂ (Subtype.val : D.U → G1 K n))
  have hmem : ∀ f : G1 K n → ℂ, Continuous f → D.Fix f → ∀ g, (fun u : D.U => f (g * u)) ∈ V := by
    intro f hf hfix g
    refine ⟨fun x => f (g * x), ⟨by fun_prop, fun y => ?_⟩, rfl⟩
    simp only [← mul_assoc]
    exact hfix (g * y)
  haveI : FiniteDimensional ℂ V := by
    obtain ⟨t, ht, h⟩ := detect D.U hU D.ν D.supp D.inv D.cont
    let ev : V →ₗ[ℂ] (t → ℂ) := (LinearMap.funLeft ℂ ℂ (fun x : t => (⟨x, ht x x.2⟩ : D.U))).comp V.subtype
    refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero _).2 ?_)
    rintro ⟨_, F, ⟨hF, hfix⟩, rfl⟩ h0
    apply Subtype.ext
    funext u
    exact h F hF hfix (fun x hx => congrFun h0 ⟨x, hx⟩) u u.2
  refine ⟨_, leftRight V ?_, fun a ha => ?_, fun f hf hfix g => Submodule.subset_span ⟨_, hmem f hf hfix g, 1, by simp⟩⟩
  · rintro _ ⟨F, ⟨hF, hfix⟩, rfl⟩ g
    exact hmem F hF hfix g
  · induction ha using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨_, ⟨F, ⟨hF, hfix⟩, rfl⟩, u, rfl⟩ := hb
      refine ⟨?_, fun w => Submodule.subset_span ⟨_, ⟨F, ⟨hF, hfix⟩, rfl⟩, w * u, by simp only [mul_assoc]⟩⟩
      exact hF.comp (continuous_subtype_val.comp (continuous_id.mul continuous_const))
    | zero => exact ⟨continuous_const, fun _ => Submodule.zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨ha.1.add hb.1, fun u => Submodule.add_mem _ (ha.2 u) (hb.2 u)⟩
    | smul c a _ ha => exact ⟨ha.1.const_smul c, fun u => Submodule.smul_mem _ c (ha.2 u)⟩
