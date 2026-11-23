import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallHeightOneExistsDvdMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem ideal_map_stalk_isPrime_of_closedPoint : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, G₁.hom x = closedPoint R' → ∀ q : Ideal R', q.IsPrime → (Ideal.map ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) q).IsPrime := by
  intro R' _ _ _ _ G₁ _ _ hG x hx q hq
  have := hG.smooth
  have := hG.geomConnected
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp G₁.left.isBasis_affineOpens
    (show x ∈ (⊤ : G₁.left.Opens) from trivial)
  replace hU : IsAffineOpen U := hU
  let A := Γ(G₁.left, U)
  let ψ : R' →+* A := (G₁.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.comp
    ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)
  have hφ : (G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom) = (G₁.left.presheaf.germ U x hxU).hom.comp ψ := by
    ext r
    rw [← TopCat.Presheaf.germ_res G₁.left.presheaf (homOfLE le_top : U ⟶ ⊤) x hxU]
    rfl
  rw [hφ, ← Ideal.map_map]
  letI : Algebra R' A := ψ.toAlgebra

  have hnu : ∀ r ∈ q, ¬ IsUnit ((G₁.left.presheaf.germ U x hxU).hom (ψ r)) := by
    intro r hr hu
    have key := DFunLike.congr_fun hφ r
    simp only [RingHom.comp_apply] at key
    rw [← key] at hu
    have hu := (Scheme.mem_basicOpen G₁.left _ x (show x ∈ (⊤ : G₁.left.Opens) from trivial)).mpr hu
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at hu
    change G₁.hom x ∈ PrimeSpectrum.basicOpen r at hu
    rw [hx] at hu
    exact hu (IsLocalRing.le_maximalIdeal hq.ne_top hr)
  set P := hU.primeIdealOf ⟨x, hxU⟩
  letI : Algebra A (G₁.left.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk G₁.left.presheaf ⟨x, hxU⟩
  haveI := hU.isLocalization_stalk ⟨x, hxU⟩
  have hle : Ideal.map ψ q ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (G₁.left.presheaf.stalk x) P.asIdeal]
    exact hnu r hr
  have hI : (Ideal.map ψ q).IsPrime := by
    haveI := hq
    have hne : Ideal.map ψ q ≠ ⊤ := fun h => P.isPrime.ne_top (top_le_iff.mp (h ▸ hle))
    let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R') A q
    haveI : Nontrivial (A ⧸ Ideal.map (algebraMap R' A) q) := Ideal.Quotient.nontrivial_iff.mpr hne
    haveI : Nontrivial (TensorProduct R' A (R' ⧸ q)) := e.symm.toEquiv.nontrivial
    have eSp : Spec.map (CommRingCat.ofHom (algebraMap R' A)) = hU.fromSpec ≫ G₁.hom := by
      apply ext_of_isAffine
      have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R' A))
      rw [← Iso.eq_comp_inv] at h1
      rw [h1, Scheme.Hom.comp_appTop]
      change _ = _ ≫ hU.fromSpec.app ⊤
      rw [IsAffineOpen.fromSpec_app_of_le hU ⊤ le_top]
      rw [show (homOfLE le_top : hU.fromSpec ⁻¹ᵁ ⊤ ⟶ ⊤) = 𝟙 _ from rfl]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      ext r
      simp [ψ, RingHom.algebraMap_toAlgebra]
    haveI : IsIntegral (Spec (CommRingCat.of (R' ⧸ q))) :=
      (affine_isIntegral_iff _).mpr (inferInstanceAs (IsDomain (R' ⧸ q)))
    haveI : IsIntegral (pullback G₁.hom (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⧸ q))))) :=
      GlobalTheory.isIntegral_pullback_of_smooth _ _
    let j := (pullbackSpecIso R' A (R' ⧸ q)).inv ≫ (pullback.congrHom eSp rfl).hom ≫
      (pullbackRightPullbackFstIso G₁.hom _ hU.fromSpec).inv ≫ pullback.snd _ _
    haveI : Nonempty (Spec (CommRingCat.of (TensorProduct R' A (R' ⧸ q)))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum _))
    haveI := isIntegral_of_isOpenImmersion j
    haveI hdom := (affine_isIntegral_iff _).mp this
    haveI : IsDomain (A ⧸ Ideal.map (algebraMap R' A) q) := MulEquiv.isDomain _ e.toRingEquiv.toMulEquiv
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  exact IsLocalization.isPrime_of_isPrime_disjoint P.asIdeal.primeCompl _ _ hI
    (Set.disjoint_left.mpr fun a ha h => ha (hle h))

end GlobalTheory.Mum
