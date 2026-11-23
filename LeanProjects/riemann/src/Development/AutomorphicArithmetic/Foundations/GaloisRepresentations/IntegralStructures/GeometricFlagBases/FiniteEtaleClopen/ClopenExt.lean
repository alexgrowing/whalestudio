import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.StalkDom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.GenDense
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.GenRange
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.IrreducibleComponents

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

private theorem exists_isClopen_preimage {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]
    (f : P → X) (hf : Topology.IsEmbedding f) (hd : Dense (Set.range f))
    (hl : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ IsPreirreducible W)
    (U : Set P) (hU : IsClopen U) : ∃ V : Set X, IsClopen V ∧ f ⁻¹' V = U := by
  have key : ∀ W : Set X, IsOpen W → IsPreirreducible W → (f ⁻¹' W ⊆ U ∨ f ⁻¹' W ⊆ Uᶜ) := by
    intro W hW hWi
    obtain ⟨A, hA, hAU⟩ := hf.isInducing.isOpen_iff.mp hU.isOpen
    obtain ⟨B, hB, hBU⟩ := hf.isInducing.isOpen_iff.mp hU.compl.isOpen
    by_contra hc
    rw [not_or, Set.not_subset, Set.not_subset] at hc
    obtain ⟨⟨a, ha, haU⟩, ⟨b, hb, hbU⟩⟩ := hc
    have h1 : (W ∩ A).Nonempty := by
      refine ⟨f b, hb, ?_⟩
      rw [← Set.mem_preimage, hAU]
      simpa using hbU
    have h2 : (W ∩ B).Nonempty := by
      refine ⟨f a, ha, ?_⟩
      rw [← Set.mem_preimage, hBU]
      exact haU
    obtain ⟨x, hxW, hxA, hxB⟩ := hWi A B hA hB h1 h2
    obtain ⟨_, ⟨q, rfl⟩, -, hqA, hqB⟩ := hd.exists_mem_open (hW.inter (hA.inter hB)) ⟨x, hxW, hxA, hxB⟩
    have hq1 : q ∈ U := by rw [← hAU]; exact hqA
    have hq2 : q ∈ Uᶜ := by rw [← hBU]; exact hqB
    exact hq2 hq1
  refine ⟨{x | ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ IsPreirreducible W ∧ f ⁻¹' W ⊆ U}, ⟨?_, ?_⟩, ?_⟩
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨W, hW, hxW, hWi⟩ := hl x
    have hWc : f ⁻¹' W ⊆ Uᶜ := by
      rcases key W hW hWi with h | h
      · exact absurd ⟨W, hW, hxW, hWi, h⟩ hx
      · exact h
    refine ⟨W, ?_, hW, hxW⟩
    rintro z hz ⟨W', hW', hzW', hW'i, hW'U⟩
    obtain ⟨_, ⟨q, rfl⟩, hqW, hqW'⟩ := hd.exists_mem_open (hW.inter hW') ⟨z, hz, hzW'⟩
    exact hWc hqW (hW'U hqW')
  · rw [isOpen_iff_forall_mem_open]
    rintro x ⟨W, hW, hxW, hWi, hWU⟩
    exact ⟨W, fun z hz => ⟨W, hW, hz, hWi, hWU⟩, hW, hxW⟩
  · ext q
    constructor
    · rintro ⟨W, -, hqW, -, hWU⟩
      exact hWU hqW
    · intro hq
      obtain ⟨W, hW, hxW, hWi⟩ := hl (f q)
      rcases key W hW hWi with h | h
      · exact ⟨W, hW, hxW, hWi, h⟩
      · exact absurd hq (h hxW)

private theorem exists_isPreirreducible_nhd (Y : Scheme.{0}) [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y)) (y : Y) :
    ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ IsPreirreducible W := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  haveI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI hN : TopologicalSpace.NoetherianSpace (U : Scheme) := noetherianSpace_of_isAffineOpen U hU
  have hdom : ∀ z : (U : Scheme), IsDomain ((U : Scheme).presheaf.stalk z) := by
    intro z
    have e := (Scheme.Opens.stalkIso U z).commRingCatIsoToRingEquiv
    haveI := hY z.1
    exact Function.Injective.isDomain e.toRingHom e.injective
  let z : (U : Scheme) := ⟨y, hyU⟩
  have hC : IsOpen (irreducibleComponent z) := by
    have h := FunctorialResolution.EmbeddedResolution.isOpen_sUnion_of_subset_irreducibleComponents
      (X := (U : Scheme)) (𝒜 := {irreducibleComponent z}) ?_ ?_
    · rwa [Set.sUnion_singleton] at h
    · rintro C₁ h1 C₂ h2 ⟨x, hx1, hx2⟩
      exact FunctorialResolution.EmbeddedResolution.irreducibleComponents_eq_of_stalk_isDomain
        (U : Scheme) hdom h1 h2 hx1 hx2
    · intro D hD
      rw [Set.mem_singleton_iff.mp hD]
      exact irreducibleComponent_mem_irreducibleComponents _
  refine ⟨U.ι '' irreducibleComponent z, U.ι.isOpenEmbedding.isOpenMap _ hC,
    ⟨z, mem_irreducibleComponent, rfl⟩, ?_⟩
  exact isIrreducible_irreducibleComponent.isPreirreducible.image _ U.ι.continuous.continuousOn

theorem UpperTheory.Gal.Int.Geo.Cut.clopenExt :
    UpperTheory.Gal.Int.Geo.Cut.ClopenExt := by
  intro O k _ _ _ _ _ _ Y p hp U hU
  have hf : Flat p := inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨hr, he⟩ := genRange O k Y p
  obtain ⟨V, hV, hVU⟩ := exists_isClopen_preimage (pullback.fst p (gen O k)) he
    (by rw [hr]; exact genDense O Y p hf)
    (exists_isPreirreducible_nhd Y (stalkDom O Y p hp)) U hU
  exact ⟨⟨V, hV.isOpen⟩, hV.isClosed, hVU⟩
