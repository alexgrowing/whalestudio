import Mathlib
open Complex Matrix
open scoped ContDiff BigOperators Real Topology

namespace GlobalTheory.PeriodicPartition

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in

theorem _root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) :
    LocallyFinite fun l : Λ => Function.support fun z : E => φ (z + l) := by
  intro x
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  have hclosed : IsClosed (Λ : Set E) :=
    AddSubgroup.isClosed_of_discrete (H := Λ.toAddSubgroup)
  have hfin : ((tsupport φ - Metric.closedBall x 1) ∩ (Λ : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (hφ.isBounded.sub Metric.isBounded_closedBall) hclosed
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  rintro l ⟨z, hz, hzb⟩
  refine ⟨?_, l.2⟩
  have hmem := Set.sub_mem_sub (subset_tsupport φ (show z + (l : E) ∈ Function.support φ from hz)) hzb
  rwa [add_sub_cancel_left] at hmem

theorem exists_periodic_bump (Λ : Submodule ℤ E) [DiscreteTopology Λ] {U : Set E}
    (hU : IsOpen U) (hper : ∀ (l : Λ) z, z ∈ U → z + l ∈ U) {x : E} (hx : x ∈ U) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ (l : Λ) z, ψ (z + l) = ψ z) ∧ tsupport ψ ⊆ U ∧
      (∀ z, 0 ≤ ψ z) ∧ 0 < ψ x := by
  obtain ⟨φ, hφU, hφc, hφs, hφr, hφx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds hx)
  have h0 : ∀ z, 0 ≤ φ z := fun z => (hφr ⟨z, rfl⟩).1
  have hlf := locallyFinite_support_translate Λ φ hφc
  refine ⟨fun z => ∑ᶠ l : Λ, φ (z + l), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← contMDiff_iff_contDiff]
    refine contMDiff_finsum (f := fun (l : Λ) (z : E) => φ (z + l)) (fun l => ?_) hlf
    rw [contMDiff_iff_contDiff]
    exact hφs.comp (contDiff_id.add contDiff_const)
  · intro l z
    show ∑ᶠ m : Λ, φ (z + l + m) = ∑ᶠ m : Λ, φ (z + m)
    rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : Λ => φ (z + m))]
    simp [add_assoc]
  · have h1 : Function.support (fun z => ∑ᶠ l : Λ, φ (z + l)) ⊆
        ⋃ l : Λ, Function.support fun z : E => φ (z + l) := by
      intro z hz
      by_contra hn
      simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
      exact hz (by simp [hn])
    refine (closure_mono h1).trans ?_
    rw [hlf.closure_iUnion]
    refine Set.iUnion_subset fun l => ?_
    have h2 : closure (Function.support fun z : E => φ (z + l)) ⊆
        (fun z : E => z + l) ⁻¹' tsupport φ :=
      closure_minimal (fun z hz => subset_tsupport _ hz)
        ((isClosed_tsupport φ).preimage (by fun_prop))
    intro z hz
    have := hper (-l) _ (hφU (h2 hz))
    simpa using this
  · exact fun z => finsum_nonneg fun l => h0 _
  · have h1 := single_le_finsum (f := fun l : Λ => φ (x + l)) 0 (hlf.point_finite x)
      (fun l => h0 _)
    simp only [ZeroMemClass.coe_zero, add_zero, hφx] at h1
    exact lt_of_lt_of_le one_pos h1

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in

theorem _root_.GlobalTheory.PeriodicPartition.exists_finite_subcover (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {κ : Type} (V : κ → Set E) (hV : ∀ k, IsOpen (V k))
    (hper : ∀ k (l : Λ) z, z ∈ V k → z + l ∈ V k) (hcov : ∀ z, ∃ k, z ∈ V k) :
    ∃ t : Finset κ, ∀ z, ∃ k ∈ t, z ∈ V k := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let b' := b.ofZLatticeBasis ℝ Λ
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b')) :=
    (ZSpan.fundamentalDomain_isBounded b').isCompact_closure
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hV (fun z _ => Set.mem_iUnion.2 (hcov z))
  refine ⟨t, fun z => ?_⟩
  obtain ⟨k, hk, hz⟩ := Set.mem_iUnion₂.1 (ht (subset_closure (ZSpan.fract_mem_fundamentalDomain b' z)))
  have hmem : (ZSpan.floor b' z : E) ∈ Λ := by
    exact (b.ofZLatticeBasis_span ℝ Λ).le (ZSpan.floor b' z).2
  refine ⟨k, hk, ?_⟩
  simpa [ZSpan.fract_apply] using hper k ⟨_, hmem⟩ _ hz

theorem exists_partition (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ι : Type} (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (hper : ∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) (hcov : ∀ z, ∃ i, z ∈ U i) :
    ∃ (s : Finset ι) (ρ : ι → E → ℝ), (∀ i, ContDiff ℝ ∞ (ρ i) ∧
      (∀ (l : Λ) z, ρ i (z + l) = ρ i z) ∧ tsupport (ρ i) ⊆ U i) ∧
      ∀ z, ∑ i ∈ s, ρ i z = 1 := by
  classical
  choose c hc using hcov
  choose ψ hψs hψp hψU hψ0 hψx using fun x => exists_periodic_bump Λ (hU (c x)) (hper (c x)) (hc x)
  obtain ⟨t, ht⟩ := exists_finite_subcover Λ (fun x => {z | 0 < ψ x z})
    (fun x => isOpen_lt continuous_const (hψs x).continuous)
    (fun x l z hz => by simpa [hψp] using hz) (fun z => ⟨z, hψx z⟩)
  have hS : ∀ z, 0 < ∑ x ∈ t, ψ x z := fun z => by
    obtain ⟨x, hx, hz⟩ := ht z
    exact Finset.sum_pos' (fun x _ => hψ0 x z) ⟨x, hx, hz⟩
  refine ⟨t.image c, fun i z => (∑ x ∈ t with c x = i, ψ x z) / ∑ x ∈ t, ψ x z,
    fun i => ⟨?_, ?_, ?_⟩, fun z => ?_⟩
  · exact (ContDiff.sum fun x _ => hψs x).div (ContDiff.sum fun x _ => hψs x) fun z => (hS z).ne'
  · intro l z
    simp only [hψp]
  · have hcl : IsClosed (⋃ x ∈ t.filter (fun x => c x = i), tsupport (ψ x)) :=
      isClosed_biUnion_finset fun x _ => isClosed_tsupport _
    refine (closure_minimal ?_ hcl).trans ?_
    · intro z hz
      by_contra hn
      refine hz ?_
      have : ∑ x ∈ t with c x = i, ψ x z = 0 := Finset.sum_eq_zero fun x hx => by
        by_contra h
        exact hn (Set.mem_iUnion₂.2 ⟨x, hx, subset_tsupport _ h⟩)
      simp only [this, zero_div]
    · refine Set.iUnion₂_subset fun x hx => ?_
      rw [← (Finset.mem_filter.1 hx).2]
      exact hψU x
  · rw [← Finset.sum_div, Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem c hx),
      div_self (hS z).ne']

end GlobalTheory.PeriodicPartition

namespace GlobalTheory

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem hasFiniteSupport_lattice_translate (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) (z : E) :
    Function.HasFiniteSupport fun l : Λ => φ (z + l) :=
  (_root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ φ hφ).point_finite z

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem contDiff_finsum_of_locallyFinite_support {ι : Type} {f : ι → E → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hlf : LocallyFinite fun i => Function.support (f i)) :
    ContDiff ℝ ∞ fun x => ∑ᶠ i, f i x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨s, hs⟩ := finsum_eventually_eq_sum hlf x
  exact (ContDiff.sum fun i _ => hf i).contDiffAt.congr_of_eventuallyEq hs

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem contDiff_finsum_lattice_translate (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) (hs : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ fun z => ∑ᶠ l : Λ, φ (z + l) :=
  contDiff_finsum_of_locallyFinite_support (fun l => hs.comp (contDiff_id.add contDiff_const))
    (_root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ φ hφ)

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem finsum_lattice_translate_add (Λ : Submodule ℤ E) (φ : E → ℝ) (l : Λ) (z : E) :
    ∑ᶠ m : Λ, φ (z + l + m) = ∑ᶠ m : Λ, φ (z + m) := by
  rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : Λ => φ (z + m))]
  simp [add_assoc]

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem tsupport_finsum_lattice_translate_subset (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (φ : E → ℝ) (hφ : HasCompactSupport φ) (U : Set E) (hU : tsupport φ ⊆ U)
    (hper : ∀ (l : Λ) z, z ∈ U → z + l ∈ U) :
    tsupport (fun z => ∑ᶠ l : Λ, φ (z + l)) ⊆ U := by
  have hlf := _root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ φ hφ
  have h1 : Function.support (fun z => ∑ᶠ l : Λ, φ (z + l)) ⊆
      ⋃ l : Λ, Function.support fun z => φ (z + l) := by
    intro z hz
    by_contra h
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at h
    exact hz (by simp [h])
  intro z hz
  have hz' := closure_mono h1 hz
  rw [hlf.closure_iUnion] at hz'
  obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hz'
  have hl' : z + l ∈ tsupport φ := tsupport_comp_subset_preimage φ (continuous_add_right (l : E)) hl
  simpa using hper (-l) _ (hU hl')

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in

theorem _root_.GlobalTheory.exists_smooth_periodic_partition_of_unity :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (ι : Type) (U : ι → Set (Fin g → ℂ)), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → ∃ (s : Finset ι) (ρ : ι → (Fin g → ℂ) → ℝ), (∀ i, ContDiff ℝ ∞ (ρ i) ∧ (∀ (l : Λ) z, ρ i (z + l) = ρ i z) ∧ tsupport (ρ i) ⊆ U i) ∧ ∀ z, ∑ i ∈ s, ρ i z = 1 := by
  intro g Λ hdisc hspan ι U hU hper hcov
  haveI := hdisc
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.PeriodicPartition.exists_finite_subcover Λ
    (fun x : Fin g → ℂ => {z | ∃ l : Λ, z + (l : Fin g → ℂ) ∈ Metric.ball x 1})
    (fun x => by
      have hset : {z | ∃ l : Λ, z + (l : Fin g → ℂ) ∈ Metric.ball x 1} =
          ⋃ l : Λ, (· + (l : Fin g → ℂ)) ⁻¹' Metric.ball x 1 := by
        ext z; simp
      rw [hset]
      exact isOpen_iUnion fun l => Metric.isOpen_ball.preimage (continuous_add_right _))
    (fun x l z ⟨m, hm⟩ => ⟨m - l, by
      have hzm : z + (l : Fin g → ℂ) + ((m - l : Λ) : Fin g → ℂ) = z + m := by push_cast; abel
      rw [hzm]
      exact hm⟩)
    (fun z => ⟨z, 0, by simp⟩)
  let β : (Fin g → ℂ) → (Fin g → ℂ) → ℝ := fun x => ⇑(⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump x)
  let θ : (Fin g → ℂ) → ℝ := fun z => ∑ x ∈ t, β x z
  have hθs : ContDiff ℝ ∞ θ := ContDiff.sum fun x _ => ContDiffBump.contDiff _
  have hθc : HasCompactSupport θ := by
    have hθeq : θ = ∑ x ∈ t, β x := by
      funext z
      simp [θ, Finset.sum_apply]
    rw [hθeq]
    exact HasCompactSupport.finset_sum fun x _ => ContDiffBump.hasCompactSupport _
  have hθn : ∀ z, 0 ≤ θ z := fun z => Finset.sum_nonneg fun x _ => ContDiffBump.nonneg _
  have hθ1 : ∀ x ∈ t, ∀ y ∈ Metric.ball x 1, 1 ≤ θ y := by
    intro x hx y hy
    have h := Finset.single_le_sum (f := fun x => β x y) (fun x _ => ContDiffBump.nonneg _) hx
    have h1 : β x y = 1 := ContDiffBump.one_of_mem_closedBall _ (Metric.ball_subset_closedBall hy)
    show 1 ≤ ∑ x ∈ t, β x y
    linarith
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin g → ℂ) isClosed_univ U hU
    (fun z _ => Set.mem_iUnion.2 (hcov z))
  have hps : ∀ i, ContDiff ℝ ∞ (p i) := fun i => contMDiff_iff_contDiff.1 (p i).contMDiff
  have hsfin := p.locallyFinite.finite_nonempty_inter_compact hθc
  let s := hsfin.toFinset
  have hkey : ∀ y, θ y * ∑ i ∈ s, p i y = θ y := by
    intro y
    by_cases hy : θ y = 0
    · simp [hy]
    · have hsum : ∑ᶠ i, p i y = ∑ i ∈ s, p i y := by
        apply finsum_eq_sum_of_support_subset
        intro i hi
        simp only [s, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
        exact ⟨y, hi, subset_tsupport _ hy⟩
      rw [← hsum, p.sum_eq_one (Set.mem_univ y), mul_one]
  let a : ι → (Fin g → ℂ) → ℝ := fun i z => θ z * p i z
  have has : ∀ i, ContDiff ℝ ∞ (a i) := fun i => hθs.mul (hps i)
  have hac : ∀ i, HasCompactSupport (a i) := fun i => hθc.mul_right
  have hat : ∀ i, tsupport (a i) ⊆ U i := fun i => tsupport_mul_subset_right.trans (hp i)
  let Θ : (Fin g → ℂ) → ℝ := fun z => ∑ᶠ l : Λ, θ (z + l)
  have hΘpos : ∀ z, 0 < Θ z := by
    intro z
    obtain ⟨x, hx, l, hl⟩ := ht z
    exact lt_of_lt_of_le one_pos ((hθ1 x hx _ hl).trans
      (single_le_finsum l (hasFiniteSupport_lattice_translate Λ θ hθc z) fun m => hθn _))
  have hΘs : ContDiff ℝ ∞ Θ := contDiff_finsum_lattice_translate Λ θ hθc hθs
  refine ⟨s, fun i z => (∑ᶠ l : Λ, a i (z + l)) / Θ z, fun i => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (contDiff_finsum_lattice_translate Λ (a i) (hac i) (has i)).div hΘs fun z => (hΘpos z).ne'
  · intro l z
    simp only [Θ]
    rw [finsum_lattice_translate_add, finsum_lattice_translate_add]
  · show tsupport (fun z => (∑ᶠ l : Λ, a i (z + l)) / Θ z) ⊆ U i
    have hfun : (fun z => (∑ᶠ l : Λ, a i (z + l)) / Θ z) =
        fun z => (∑ᶠ l : Λ, a i (z + l)) * (Θ z)⁻¹ := by
      ext z; rw [div_eq_mul_inv]
    rw [hfun]
    exact tsupport_mul_subset_left.trans
      (tsupport_finsum_lattice_translate_subset Λ (a i) (hac i) (U i) (hat i) (hper i))
  · intro z
    show ∑ i ∈ s, (∑ᶠ l : Λ, a i (z + l)) / Θ z = 1
    rw [← Finset.sum_div, div_eq_one_iff_eq (hΘpos z).ne',
      ← finsum_sum_comm s (fun (l : Λ) i => a i (z + l))
        (fun i _ => hasFiniteSupport_lattice_translate Λ (a i) (hac i) z)]
    apply finsum_congr
    intro l
    simp only [a]
    rw [← Finset.mul_sum]
    exact hkey _

end GlobalTheory
