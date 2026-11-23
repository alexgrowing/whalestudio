import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.StatementLoc
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

namespace GlobalTheory.ContCocycleDualLattice

universe u

section

variable {O G VT VT' : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT')

theorem mem_dualLat_iff_of_span (s : Finset VT) (hs : Submodule.span O (s : Set VT) = D.T) (f : VT') :
    f ∈ D.T' ↔ ∀ x ∈ s, D.bT x f ∈ Set.range (algebraMap O (FractionRing O)) := by
  constructor
  · intro hf x hx
    have := hf x (hs ▸ Submodule.subset_span hx)
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact ⟨y, hy⟩
  · intro hf x hx
    rw [← hs] at hx
    have hle : Submodule.span O (s : Set VT) ≤
        (1 : Submodule O (FractionRing O)).comap (D.bT.flip f) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨y, hy⟩ := hf x hx
      exact Submodule.mem_one.2 ⟨y, hy⟩
    exact hle hx

theorem isOpen_dualLat (hO : IsOpen (Set.range (algebraMap O (FractionRing O)))) (hT : D.T.FG) :
    IsOpen (D.T' : Set VT') := by
  obtain ⟨s, hs⟩ := hT
  have e : (D.T' : Set VT') = ⋂ x ∈ s, (fun f => D.bT x f) ⁻¹' Set.range (algebraMap O (FractionRing O)) := by
    ext f
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
    exact mem_dualLat_iff_of_span D s hs f
  rw [e]
  refine isOpen_biInter_finset fun x _ => hO.preimage ?_
  exact D.contbT.comp (continuous_const.prodMk continuous_id)

theorem exists_smul_mem_dualLat (hT : D.T.FG) (f : VT') : ∃ c : O, c ≠ 0 ∧ c • f ∈ D.T' := by
  obtain ⟨s, hs⟩ := hT
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) s (fun x => D.bT x f)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, (mem_dualLat_iff_of_span D s hs _).2 fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hb x hx
  refine ⟨y, ?_⟩
  rw [map_smul]
  exact hy

theorem exists_smul_subset_dualLat (hO : IsOpen (Set.range (algebraMap O (FractionRing O))))
    (hT : D.T.FG) {S : Set VT'} (hS : IsCompact S) : ∃ c : O, c ≠ 0 ∧ ∀ f ∈ S, c • f ∈ D.T' := by
  classical
  choose c hc0 hc using exists_smul_mem_dualLat D hT
  have hopen : IsOpen (D.T' : Set VT') := isOpen_dualLat D hO hT
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun v => (fun w : VT' => c v • w) ⁻¹' (D.T' : Set VT'))
    (fun v => hopen.preimage (continuous_const_smul (c v))) (fun f _ => Set.mem_iUnion.2 ⟨f, hc f⟩)
  refine ⟨∏ v ∈ t, c v, Finset.prod_ne_zero_iff.2 fun v _ => hc0 v, fun f hf => ?_⟩
  obtain ⟨v, hv, hfv⟩ := Set.mem_iUnion₂.1 (ht hf)
  rw [← Finset.mul_prod_erase t c hv, mul_comm, mul_smul]
  exact D.T'.smul_mem _ hfv

theorem exists_smul_mem_range_j' [CompactSpace G]
    (hO : IsOpen (Set.range (algebraMap O (FractionRing O)))) (hT : D.T.FG) (y : H1 D.ρT') :
    ∃ c : O, c ≠ 0 ∧ c • y ∈ LinearMap.range D.j' := by
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨c, hc0, hc⟩ := exists_smul_subset_dualLat D hO hT (isCompact_range z.2.1)
    let z' : Z1 D.ρTl' := ⟨fun g => ⟨c • z.1 g, hc _ ⟨g, rfl⟩⟩,
      Continuous.subtype_mk (z.2.1.const_smul c) _, fun g h => by
        apply Subtype.ext
        show c • z.1 (g * h) = c • z.1 g + D.ρT' g (c • z.1 h)
        rw [z.2.2 g h, map_smul, smul_add]⟩
    refine ⟨c, hc0, Submodule.Quotient.mk z', ?_⟩
    rw [← Submodule.Quotient.mk_smul]
    rfl

end

end GlobalTheory.ContCocycleDualLattice

namespace GlobalTheory

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

theorem jSpan_holds : ReciprocityTheory.ChartRestriction.T2.JSpan := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ _ hF i D hD y
  haveI : IsGalois K (PadicAlgCl p) := by
    have : IsGalois ℚ_[p] (PadicAlgCl p) := inferInstance
    infer_instance
  haveI : CompactSpace (Formalism.GaloisCohomology.GK p K) := inferInstance
  haveI : CompactSpace G := i.symm.surjective.compactSpace i.symm.continuous
  exact ContCocycleDualLattice.exists_smul_mem_range_j' D hF.emb.isOpen_range hD.lat.1 y

end GlobalTheory
