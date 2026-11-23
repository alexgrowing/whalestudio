import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StBoundedGenerators
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StReducedBasisBound
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StArchCovolumeBound
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StMajorantTransport

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem BoundedGenerators.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (hR : ReducedBasisBound.Statement) (hA : ArchCovolumeBound.Statement h v)
    (hT : MajorantTransport.Statement h v) : BoundedGenerators.Statement h v := by
  intro M D t ht
  obtain ⟨c, hc⟩ := hA D
  obtain ⟨d, κ, hκ⟩ := hT M
  obtain ⟨C, hC⟩ := hR d t (|κ| * c) ht
  refine ⟨d, C, fun La g hLa hmin => ?_⟩
  obtain ⟨_, _, hcov⟩ := hc La hLa
  obtain ⟨T, hTn, hTc⟩ := hκ g

  let Φ : W →+ EuclideanSpace ℝ (Fin d) :=
    ((T : (InfinitePlace E → ι → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin d)) : _ →ₗ[ℝ] _).toAddMonoidHom.comp
      (vecAtHom v)
  have hΦ : ∀ x, Φ x = T (vecAt v x) := fun x => rfl
  have hvec : Function.Injective (vecAt v) := by
    intro x y hxy
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
    apply v.repr.injective
    ext i
    exact w.embedding.injective (congrFun (congrFun hxy w) i)
  have hΦinj : Function.Injective Φ := T.injective.comp hvec
  let L := ZLattice.comap ℝ (archLattice v La) T.symm.toLinearMap
  have hmemL : ∀ z, z ∈ L ↔ ∃ x ∈ La, Φ x = z := by
    intro z
    rw [← SetLike.mem_coe, ZLattice.coe_comap, Set.mem_preimage, SetLike.mem_coe, mem_archLattice]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    rw [hΦ]
    constructor
    · intro hx; rw [hx]; simp
    · intro hx; rw [← hx]; simp
  have hLmin : ∀ z ∈ L, z ≠ 0 → t ≤ ‖z‖ := by
    intro z hz hz0
    obtain ⟨x, hx, rfl⟩ := (hmemL z).1 hz
    have hx0 : x ≠ 0 := by rintro rfl; exact hz0 (map_zero Φ)
    rw [hΦ, hTn]
    exact hmin x hx hx0
  have hLcov : ZLattice.covolume L ≤ |κ| * c := by
    rw [hTc]
    have h0 : 0 ≤ ZLattice.covolume (archLattice v La) := ENNReal.toReal_nonneg
    exact (mul_le_mul_of_nonneg_right (le_abs_self κ) h0).trans
      (mul_le_mul_of_nonneg_left hcov (abs_nonneg κ))
  obtain ⟨b, hb⟩ := hC L hLmin hLcov
  choose e he heb using fun i => (hmemL (b i)).1 (b i).2
  refine ⟨e, le_antisymm ((AddSubgroup.closure_le La).2 (Set.range_subset_iff.2 he)) ?_,
    fun i => ?_⟩
  · intro x hx
    have hxL : Φ x ∈ L := (hmemL _).2 ⟨x, hx, rfl⟩
    have hsum := congrArg Subtype.val (b.sum_repr ⟨Φ x, hxL⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    set r := b.repr ⟨Φ x, hxL⟩
    have hx' : x = ∑ i, r i • e i := by
      apply hΦinj
      rw [← hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, heb i]
    rw [hx']
    exact AddSubgroup.sum_mem _ fun i _ =>
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  · rw [← hTn, ← hΦ, heb i]
    exact hb i

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
