import Development.EtaleCohomology.EtaleSheaves.LeafCloseBCut
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

open AlgebraicGeometry CategoryTheory LateralTheory.E.E4 Topology

namespace LateralTheory.E.LeafDimOpenPf

theorem dim_mono {X : Type*} [TopologicalSpace X] {S T : Set X} (h : S ⊆ T) :
    topologicalKrullDim S ≤ topologicalKrullDim T :=
  (IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

theorem dim_basicOpen (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (g : A) (hg : g ≠ 0) {n : ℕ} (hn : Algebra.trdeg k A = n) :
    topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) = n := by
  let B := Localization.Away g
  have hle : Submonoid.powers g ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors hg
  have : IsDomain B := IsLocalization.isDomain_localization hle
  have : Algebra.FiniteType A B := inferInstance
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective B hle)
  have : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B (Submonoid.powers g)
  have htr : Algebra.trdeg k B = n := by
    rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top k A B, hn]
  rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
      (PrimeSpectrum.localization_away_isOpenEmbedding B g).isEmbedding
      (PrimeSpectrum.localization_away_comap_range B g),
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, GlobalTheory.ringKrullDim_eq_of_trdeg_eq k B htr]

theorem LeafDimOpen_of : LateralTheory.E.LeafCloseBCut.LeafDimOpen := by
  intro k _ X b _ hX U hU hne
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨A0, _, _, _, _, _, j0, _, ⟨p0, hp0⟩, -, htr0⟩ := GlobalTheory.exists_affine_chart_trdeg_eq b x0
  obtain ⟨n, -, htn⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k A0
  have hK := htr0.symm.trans htn
  have hup : topologicalKrullDim X ≤ n := by
    refine GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨A, _, _, _, _, _, j, _, hx, -, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq b x
    refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, le_of_eq ?_⟩
    rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding j.isOpenEmbedding.isEmbedding rfl]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans
      (GlobalTheory.ringKrullDim_eq_of_trdeg_eq k A (htr.trans hK))
  refine hup.trans ?_
  have hVo : IsOpen (j0 ⁻¹' U) := hU.preimage j0.isOpenEmbedding.continuous
  have hpV : p0 ∈ j0 ⁻¹' U := by simpa [Set.mem_preimage, hp0] using hx0
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpV hVo
  have hg : g ≠ 0 := by
    rintro rfl; exact (PrimeSpectrum.mem_basicOpen _ _).mp hpg (Ideal.zero_mem _)
  have hd := dim_basicOpen k A0 g hg htn
  calc (n : WithBot ℕ∞) = topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A0)) := hd.symm
    _ = topologicalKrullDim (j0 '' (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A0))) :=
      (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
        (j0.isOpenEmbedding.isEmbedding.comp IsEmbedding.subtypeVal)
        (by rw [Set.range_comp]; exact congrArg _ Subtype.range_coe)).symm
    _ ≤ topologicalKrullDim U := dim_mono (by rintro _ ⟨q, hq, rfl⟩; exact hsub hq)

end LateralTheory.E.LeafDimOpenPf
