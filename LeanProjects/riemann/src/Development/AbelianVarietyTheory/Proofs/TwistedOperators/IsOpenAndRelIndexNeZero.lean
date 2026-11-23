import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.LatOpen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}

theorem eventually_smul_mem (L : Submodule 𝒪[k] (ι → k))
    (hL : Submodule.span k (L : Set (ι → k)) = ⊤) (x : ι → k) :
    ∀ᶠ t in nhds (0 : k), t • x ∈ L := by
  have hx : x ∈ Submodule.span k (L : Set (ι → k)) := by rw [hL]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have h : (𝒪[k] : Set k) ∈ nhds (0 : k) := (isOpen_int k).mem_nhds (zero_mem 𝒪[k])
    filter_upwards [h] with t ht
    exact L.smul_mem (⟨t, ht⟩ : 𝒪[k]) hy
  | zero => exact Filter.Eventually.of_forall fun t => by simp
  | add y z _ _ hy hz =>
    filter_upwards [hy, hz] with t h1 h2
    rw [smul_add]
    exact L.add_mem h1 h2
  | smul a y _ hy =>
    have ht : Filter.Tendsto (fun t : k => t * a) (nhds 0) (nhds 0) := by
      have h : Continuous (fun t : k => t * a) := continuous_id.mul continuous_const
      simpa using h.tendsto 0
    filter_upwards [ht.eventually hy] with t h
    rwa [smul_smul]

theorem isOpen_of_span_eq_top [Fintype ι] [DecidableEq ι] (L : Submodule 𝒪[k] (ι → k))
    (hL : Submodule.span k (L : Set (ι → k)) = ⊤) : IsOpen (L : Set (ι → k)) := by
  refine AddSubgroup.isOpen_of_mem_nhds L.toAddSubgroup (g := 0) ?_
  have h : ∀ᶠ x in nhds (0 : ι → k), ∀ i, x i • (Pi.single i (1 : k) : ι → k) ∈ L := by
    refine Filter.eventually_all.2 fun i => ?_
    have ht : Filter.Tendsto (fun x : ι → k => x i) (nhds 0) (nhds 0) :=
      (continuous_apply i).tendsto (0 : ι → k)
    exact ht.eventually (eventually_smul_mem L hL _)
  filter_upwards [h] with x hx
  have e : x = ∑ i, x i • (Pi.single i (1 : k) : ι → k) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  change x ∈ L
  rw [e]
  exact L.sum_mem fun i _ => hx i

theorem isCompact_stdLat : IsCompact (stdLat k ι : Set (ι → k)) := by
  have e : (stdLat k ι : Set (ι → k)) = Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
    ext v
    simp only [SetLike.mem_coe, mem_stdLat, Set.mem_pi, Set.mem_univ, true_imp_iff]
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_int k

theorem isOpen_and_relIndex_ne_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι]
    (L : Submodule 𝒪[k] (ι → k)) (hL : Submodule.IsLattice k L) :
    IsOpen (L : Set (ι → k)) ∧ L.toAddSubgroup.relIndex (stdLat k ι).toAddSubgroup ≠ 0 := by
  have ho := isOpen_of_span_eq_top L hL.span_eq_top
  refine ⟨ho, ?_⟩
  haveI : CompactSpace (stdLat k ι).toAddSubgroup :=
    isCompact_iff_compactSpace.1 (isCompact_stdLat (k := k) (ι := ι))
  haveI : Finite ((stdLat k ι).toAddSubgroup ⧸
      L.toAddSubgroup.addSubgroupOf (stdLat k ι).toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen _ (ho.preimage continuous_subtype_val)
  exact AddSubgroup.index_ne_zero_of_finite

end GlobalTheory.RootEx.LatOpen
