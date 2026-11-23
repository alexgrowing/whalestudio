import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimGen
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

set_option backward.isDefEq.respectTransparency false

private theorem isFractionRing_residueField {O : Type} [CommRing O] [IsDomain O]
    (p : PrimeSpectrum O) (hp : p.asIdeal = ⊥) : IsFractionRing O p.asIdeal.ResidueField := by
  obtain ⟨p, _⟩ := p
  obtain rfl : p = ⊥ := hp
  infer_instance

private theorem exists_ringEquiv_residueField (O K : Type) [CommRing O] [IsDomain O] [Field K]
    [Algebra O K] [IsFractionRing O K] (x : Sp O) (hx : x.asIdeal = ⊥) :
    ∃ ε : K ≃+* (Sp O).residueField x,
      spMap ε.toRingHom ≫ spMap (algebraMap O K) = (Sp O).fromSpecResidueField x := by
  have := isFractionRing_residueField (O := O) x hx
  let e : K ≃ₐ[O] x.asIdeal.ResidueField := IsLocalization.algEquiv (nonZeroDivisors O) _ _
  refine ⟨e.toRingEquiv.trans
    (Scheme.Spec.residueFieldIso (CommRingCat.of O) x).commRingCatIsoToRingEquiv.symm, ?_⟩
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  ext a
  exact congrArg (Scheme.Spec.residueFieldIso (CommRingCat.of O) x).inv.hom (e.commutes a)

private theorem isOpenImmersion_spMap (O K : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] :
    IsOpenImmersion (spMap (algebraMap O K)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have : IsLocalization.Away ϖ K := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ) (nonZeroDivisors O)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero) fun a ha ↦ ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (nonZeroDivisors.ne_zero ha) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact IsOpenImmersion.of_isLocalization ϖ

theorem UpperTheory.generic_fibre_open_projective :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (B : GlobalTheory.Vert.Model O), IsIntegral B.toBase.genFibre ∧ IsOpenImmersion B.toBase.genFibreι ∧ Set.range B.toBase.genFibreι = B.gen ∧ IsProjOver B.toBase.genFibreStr ∧ topologicalKrullDim B.toBase.genFibre = B.relDim ∧ ∃ ε : K ≃+* B.toBase.fnField, B.toBase.genFibreStr ≫ spMap ε.toRingHom ≫ spMap (algebraMap O K) = B.toBase.genFibreι ≫ B.str := by
  intro O K _ _ _ _ _ _ B
  have hx : (genericPoint (Vert.Model.base O).X).asIdeal = ⊥ :=
    Vert.Model.mem_gen_iff_eq_bot.1 (Vert.Model.base O).genericPoint_mem_gen
  obtain ⟨ε, hε⟩ := exists_ringEquiv_residueField O K (genericPoint (Vert.Model.base O).X) hx
  have H : IsPullback B.toBase.genFibreι B.toBase.genFibreStr B.str
      ((Sp O).fromSpecResidueField (genericPoint (Vert.Model.base O).X)) :=
    B.toBase.isPullback_genFibre
  have hK := isOpenImmersion_spMap O K
  have hiso : IsIso (spMap ε.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map ε.toCommRingCatIso.hom))
  have hφ : IsOpenImmersion ((Sp O).fromSpecResidueField (genericPoint (Vert.Model.base O).X)) := by
    rw [← hε]; infer_instance
  have hι : IsOpenImmersion B.toBase.genFibreι :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) H.flip hφ
  have hr : Set.range B.toBase.genFibreι = B.gen := by
    refine (B.toBase.f.range_fiberι _).trans (Set.ext fun y => ?_)
    refine Iff.trans ?_ (Vert.Model.mem_gen_iff_eq_bot (Z := B) (x := y)).symm
    exact ⟨fun h => (congrArg PrimeSpectrum.asIdeal h).trans hx,
      fun h => PrimeSpectrum.ext (h.trans hx.symm)⟩
  refine ⟨isIntegral_of_isOpenImmersion B.toBase.genFibreι, hι, hr, ?_, ?_, ε, ?_⟩
  · have H' := H
    rw [← hε, ← Spec.map_comp] at H'
    exact ProjSpace.isProjOver_of_isPullback_spMap (ε.toRingHom.comp (algebraMap O K)) H'
      B.isProjOver
  · rw [← Vert.Model.topologicalKrullDim_gen O B]
    exact (topologicalKrullDim_eq_of_isEmbedding
      B.toBase.genFibreι.isOpenEmbedding.isEmbedding hr).symm
  · rw [hε]; exact H.w.symm
