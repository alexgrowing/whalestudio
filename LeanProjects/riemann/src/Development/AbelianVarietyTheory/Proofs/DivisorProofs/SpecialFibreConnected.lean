import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickFibIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEqOfBasicOpenEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperFlatAdicSectionsLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperFlatSectionEqZeroOfThickeningsStatement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

noncomputable section

namespace GlobalTheory.SpecialConn

theorem range_spec_map_eq {O S : Type} [CommRing O] [IsLocalRing O] [CommRing S] [Nontrivial S] (φ : O →+* S)
    (hφ : ∀ Q : Ideal S, Q.IsPrime → IsLocalRing.maximalIdeal O ≤ Q.comap φ) :
    Set.range (Spec.map (CommRingCat.ofHom φ)) = {IsLocalRing.closedPoint O} := by
  have key : ∀ Q : PrimeSpectrum S, Spec.map (CommRingCat.ofHom φ) Q = IsLocalRing.closedPoint O := by
    intro Q
    refine PrimeSpectrum.ext ?_
    change Q.asIdeal.comap φ = IsLocalRing.maximalIdeal O
    exact le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap φ).ne_top) (hφ _ Q.2)
  ext x
  constructor
  · rintro ⟨Q, rfl⟩
    exact key Q
  · rintro rfl
    obtain ⟨M, hM⟩ := Ideal.exists_maximal S
    exact ⟨⟨M, hM.isPrime⟩, key _⟩

theorem range_thickQ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Set.range (Spec.map (CommRingCat.ofHom (thickQ O n))) = {IsLocalRing.closedPoint O} := by
  haveI : Nontrivial (O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal O).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero n)))
  refine range_spec_map_eq _ fun Q hQ => ?_
  have h : IsLocalRing.maximalIdeal O ^ (n + 1) ≤ Q.comap (thickQ O n) := fun a ha => by
    change Ideal.Quotient.mk _ a ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact Q.zero_mem
  exact (Ideal.IsPrime.comap (thickQ O n)).le_of_pow_le h

theorem range_residue (O : Type) [CommRing O] [IsLocalRing O] :
    Set.range (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) = {IsLocalRing.closedPoint O} := by
  refine range_spec_map_eq _ fun Q hQ a ha => ?_
  change IsLocalRing.residue O a ∈ Q
  rw [(IsLocalRing.residue_eq_zero_iff a).2 ha]
  exact Q.zero_mem

theorem connectedSpace_specialFibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)), IsIntegral Y → (∀ z : Y, IsIntegrallyClosed (Y.presheaf.stalk z)) → IsProper f → Flat f → ConnectedSpace (specialFibre f) := by
  intro O _ _ _ _ Y f hY _ hP hF
  have hT : Set.range (specialι f) = f ⁻¹' {IsLocalRing.closedPoint O} := by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    rw [range_residue] at h
    exact h
  have hTn : ∀ n, Set.range (thickι f n) = f ⁻¹' {IsLocalRing.closedPoint O} := fun n => by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (thickQ O n)))
    rw [range_thickQ] at h
    exact h
  have hne : ∃ y : Y, f y = IsLocalRing.closedPoint O := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    let η : Spec (.of O) := ⟨⊥, Ideal.bot_prime⟩
    have hgen : η ⤳ f y := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    obtain ⟨y', -, hy'⟩ := (Flat.generalizingMap f) hgen
    have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hsp : η ⤳ IsLocalRing.closedPoint O :=
      (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    exact hsp.mem_closed hc ⟨y', hy'⟩
  obtain ⟨y₀, hy₀⟩ := hne
  have hy₀' : y₀ ∈ Set.range (specialι f) := by rw [hT]; exact hy₀
  obtain ⟨z₀, -⟩ := hy₀'
  haveI : Nonempty (specialFibre f) := ⟨z₀⟩
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  haveI : IsClosedImmersion (specialι f) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))))
  have hcl : Topology.IsClosedEmbedding (specialι f) := (specialι f).isClosedEmbedding
  refine { toPreconnectedSpace := preconnectedSpace_iff_clopen.2 fun U hU => ?_, toNonempty := ‹_› }
  by_contra hcon
  push_neg at hcon
  obtain ⟨hU0, hU1⟩ := hcon
  obtain ⟨u, hu⟩ := hU0
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ U := by
    by_contra h
    push_neg at h
    exact hU1 (Set.eq_univ_of_forall h)
  let A := specialι f '' U
  let B := specialι f '' Uᶜ
  have hA : IsClosed A := hcl.isClosedMap _ hU.1
  have hB : IsClosed B := hcl.isClosedMap _ hU.2.isClosed_compl
  have hpt : ∀ n (z : specialFibre f), ∃ x, thickι f n x = specialι f z := fun n z => by
    have : specialι f z ∈ Set.range (thickι f n) := by rw [hTn, ← hT]; exact ⟨z, rfl⟩
    exact this
  have hAB : ∀ n, (thickι f n ⁻¹' A)ᶜ = thickι f n ⁻¹' B := by
    intro n
    ext x
    obtain ⟨z, hz⟩ : thickι f n x ∈ Set.range (specialι f) := by rw [hT, ← hTn n]; exact ⟨x, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, A, B, Set.mem_image]
    constructor
    · intro h
      exact ⟨z, fun hzU => h ⟨z, hzU, hz⟩, hz⟩
    · rintro ⟨w, hw, hw'⟩ ⟨w', hw'U, hw''⟩
      exact hw (hcl.injective (hw''.trans hw'.symm) ▸ hw'U)
  have hclo : ∀ n, IsClopen (thickι f n ⁻¹' A) := fun n =>
    ⟨hA.preimage (thickι f n).continuous,
      by rw [← isClosed_compl_iff, hAB n]; exact hB.preimage (thickι f n).continuous⟩
  choose e he hbe using fun n => GlobalTheory.T.exists_idempotent_of_clopen _ _ (hclo n)
  have hcomp : ∀ n, (thickTr f n).appTop.hom (e (n + 1)) = e n := by
    intro n
    refine GlobalTheory.T.idempotent_eq_of_basicOpen_eq' _ _ _ (by rw [← map_mul, he]) (he n) ?_
    refine TopologicalSpace.Opens.ext ?_
    rw [← Scheme.Hom.preimage_basicOpen_top, hbe n]
    change thickTr f n ⁻¹' ((Scheme.basicOpen _ (e (n + 1)) : Set _)) = _
    rw [hbe (n + 1), ← Set.preimage_comp, ← thickTr_ι f n]
    rfl
  obtain ⟨s, hs⟩ := GlobalTheory.T.proper_flat_adic_sections_lift O Y f e hcomp
  have hss : s * s = s := by
    have := GlobalTheory.T.proper_flat_section_eq_zero_of_thickenings O Y f (s * s - s) fun n => by rw [map_sub, map_mul, hs, he, sub_self]
    exact sub_eq_zero.1 this
  have h01 : s = 0 ∨ s = 1 := IsIdempotentElem.iff_eq_zero_or_one.1 hss
  obtain ⟨x, hx⟩ := hpt 0 u
  obtain ⟨x', hx'⟩ := hpt 0 u'
  rcases h01 with h0 | h1
  · have e0 : e 0 = 0 := by rw [← hs 0, h0, map_zero]
    have hxA : x ∈ thickι f 0 ⁻¹' A := ⟨u, hu, hx.symm⟩
    rw [← hbe 0, e0, Scheme.basicOpen_zero] at hxA
    exact hxA
  · have e1 : e 0 = 1 := by rw [← hs 0, h1, map_one]
    have hxA : x' ∈ ((thickFib f 0).basicOpen (e 0) : Set _) := by
      rw [e1, Scheme.basicOpen_one]
      trivial
    rw [hbe 0] at hxA
    obtain ⟨w, hw, hw'⟩ := hxA
    exact hu' (hcl.injective (hw'.trans hx') ▸ hw)

end GlobalTheory.SpecialConn
