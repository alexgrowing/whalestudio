import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenBasicOpenSpecProdSelfFirstIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSpecProdSelfPreimageEqClopenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtSpecProdSelfOfBasicOpenPreimageEqStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.AlgConn

theorem connectedSpace_specialFibre_of_morphisms : GlobalTheory.Published.FormalAlgebraisation.Morphisms →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)),
      IsProper f → ConnectedSpace ↑Y → ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f) := by
  intro H O _ _ _ hI Y f hP hY
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hT : Set.range (specialι f) = f ⁻¹' {IsLocalRing.closedPoint O} := by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    rw [range_residue] at h
    exact h
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hTn : ∀ n, Set.range (thickι f n) = f ⁻¹' {IsLocalRing.closedPoint O} := fun n => by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (thickQ O n)))
    rw [range_thickQ] at h
    exact h
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hne : ∃ y : Y, f y = IsLocalRing.closedPoint O := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hsp : f y ⤳ IsLocalRing.closedPoint O :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (f y).2.ne_top)
    exact hsp.mem_closed hc ⟨y, rfl⟩
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  obtain ⟨y₀, hy₀⟩ := hne
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hy₀' : y₀ ∈ Set.range (specialι f) := by rw [hT]; exact hy₀
  obtain ⟨z₀, -⟩ := hy₀'
  haveI : Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f) := ⟨z₀⟩
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  haveI : IsClosedImmersion (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))))
  have hcl : Topology.IsClosedEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f) :=
    (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f).isClosedEmbedding
  refine { toPreconnectedSpace := preconnectedSpace_iff_clopen.2 fun U hU => ?_, toNonempty := ‹_› }
  by_contra hcon
  push_neg at hcon
  obtain ⟨hU0, hU1⟩ := hcon
  obtain ⟨u, hu⟩ := hU0
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ U := by
    by_contra h
    push_neg at h
    exact hU1 (Set.eq_univ_of_forall h)
  let A := GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f '' U
  let B := GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f '' Uᶜ
  have hA : IsClosed A := hcl.isClosedMap _ hU.1
  have hB : IsClosed B := hcl.isClosedMap _ hU.2.isClosed_compl
  have hpt : ∀ n (z : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f), ∃ x, GlobalTheory.SpecialConn.thickι f n x =
      GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f z := fun n z => by
    have : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f z ∈ Set.range (GlobalTheory.SpecialConn.thickι f n) := by
      rw [hTn, ← hT]; exact ⟨z, rfl⟩
    exact this
  have hAB : ∀ n, (GlobalTheory.SpecialConn.thickι f n ⁻¹' A)ᶜ = GlobalTheory.SpecialConn.thickι f n ⁻¹' B := by
    intro n
    ext x
    obtain ⟨z, hz⟩ : GlobalTheory.SpecialConn.thickι f n x ∈ Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f) := by
      rw [hT, ← hTn n]; exact ⟨x, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, A, B, Set.mem_image]
    constructor
    · intro h
      exact ⟨z, fun hzU => h ⟨z, hzU, hz⟩, hz⟩
    · rintro ⟨w, hw, hw'⟩ ⟨w', hw'U, hw''⟩
      exact hw (hcl.injective (hw''.trans hw'.symm) ▸ hw'U)
  have hclo : ∀ n, IsClopen (GlobalTheory.SpecialConn.thickι f n ⁻¹' A) := fun n =>
    ⟨hA.preimage (GlobalTheory.SpecialConn.thickι f n).continuous,
      by rw [← isClosed_compl_iff, hAB n]; exact hB.preimage (GlobalTheory.SpecialConn.thickι f n).continuous⟩
  choose h hhp hhU using fun n => GlobalTheory.T.exists_hom_specProdSelf_preimage_eq_clopen O (GlobalTheory.SpecialConn.thickFib f n)
    (GlobalTheory.SpecialConn.thickι f n ≫ f) _ (hclo n)
  haveI : IsProper (Over.mk f).hom := hP
  haveI : IsProper (Over.mk (twoπ O)).hom := isProper_twoπ O
  have hc : ∀ n, GlobalTheory.SpecialConn.thickTr f n ≫ h (n + 1) = h n := by
    intro n
    refine GlobalTheory.T.hom_ext_specProdSelf_of_basicOpen_preimage_eq O _ _ _ ?_ ?_
    · rw [Category.assoc, hhp, hhp, ← Category.assoc, GlobalTheory.SpecialConn.thickTr_ι]
    · refine TopologicalSpace.Opens.ext ?_
      rw [hhU n]
      change GlobalTheory.SpecialConn.thickTr f n ⁻¹' ((h (n + 1) ⁻¹ᵁ _ : (GlobalTheory.SpecialConn.thickFib f (n+1)).Opens) : Set _) = _
      rw [hhU (n + 1), ← Set.preimage_comp, ← GlobalTheory.SpecialConn.thickTr_ι f n]
      rfl
  obtain ⟨g, hg, -⟩ := GlobalTheory.Published.FormalAlgebraisation.Morphisms.existsUnique_thick H hI (Over.mk f)
    (Over.mk (twoπ O)) h (fun n => hhp n) hc
  have hW : IsClopen ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) :=
    (isClopen_basicOpen_specProdSelfFirstIdempotent O).preimage g.left.continuous
  have h0 : GlobalTheory.SpecialConn.thickι f 0 ⁻¹' ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) =
      GlobalTheory.SpecialConn.thickι f 0 ⁻¹' A := by
    rw [← hhU 0, ← hg 0]
    rfl
  obtain ⟨x, hx⟩ := hpt 0 u
  obtain ⟨x', hx'⟩ := hpt 0 u'
  rcases isClopen_iff.1 hW with hW0 | hW1
  · have hxA : x ∈ GlobalTheory.SpecialConn.thickι f 0 ⁻¹' A := ⟨u, hu, hx.symm⟩
    rw [← h0, hW0] at hxA
    simp at hxA
  · have hxA : x' ∈ GlobalTheory.SpecialConn.thickι f 0 ⁻¹'
        ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) := by
      rw [hW1]; trivial
    rw [h0] at hxA
    obtain ⟨w, hw, hw'⟩ := hxA
    exact hu' (hcl.injective (hw'.trans hx') ▸ hw)

end GlobalTheory.AlgConn
