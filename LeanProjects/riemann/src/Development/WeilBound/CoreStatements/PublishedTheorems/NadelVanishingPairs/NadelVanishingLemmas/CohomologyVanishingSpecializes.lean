import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.HomologyVanishingSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.SemicontLB

open GlobalTheory.AbLaw GlobalTheory.Adelic

theorem nonempty_cechLB_homology_equiv_coh {X : Scheme.{0}} {R : Type} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (hM : M.IsLB) {κ : Type} [LinearOrder κ] [Finite κ]
    {D : κ → X.Opens} (hc : ⨆ i, D i = ⊤) (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i))
    (n : ℕ) : Nonempty ((cechLB f M D).homology n ≃ coh (LB.toMod M) n) := by
  haveI : SheafOfModules.IsQuasicoherent (LB.toMod M) := GlobalTheory.LB.isQuasicoherent_toMod hM
  letI : Algebra R Γ(X, ⊤) := algebraΓOfHom f
  exact ⟨(((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (FieldChangeInter.cechIso f M D)).toLinearEquiv.toEquiv).trans
    (cechHEquivCoh R hc hD (LB.toMod M) n).toEquiv⟩

private theorem affine_cover_preimage_of_isAffineHom {X Y : Scheme.{0}} (π : Y ⟶ X) [IsAffineHom π] {ι : Type}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hint : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) :
    (⨆ i, π ⁻¹ᵁ U i = ⊤) ∧ ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, π ⁻¹ᵁ U i) := by
  classical
  have key : ∀ s : Finset ι, ⨅ i ∈ s, π ⁻¹ᵁ U i = π ⁻¹ᵁ (⨅ i ∈ s, U i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.iInf_insert, Finset.iInf_insert, ih]; rfl
  refine ⟨?_, fun s hs => ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, hU]; rfl
  · rw [key s]; exact (hint s hs).preimage π

private theorem fibre_lemma_2 {R : Type} [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ) (q : ℕ)
    (hV : ∀ p : PrimeSpectrum R, Module.Finite p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology q))
    {κ : Type} [Field κ] (g : R →+* κ) :
    Subsingleton ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology q) ↔
      Module.finrank (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R).asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R
          (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R).asIdeal.ResidueField)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).homology q) = 0 := by
  let P : PrimeSpectrum R := ⟨RingHom.ker g, RingHom.ker_isPrime g⟩
  change _ ↔ Module.finrank P.asIdeal.ResidueField
    ((((ModuleCat.extendScalars (algebraMap R P.asIdeal.ResidueField)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology q) = 0
  haveI := hV P
  have hunit : P.asIdeal.primeCompl ≤ Submonoid.comap g (IsUnit.submonoid κ) := by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.2 fun h => hx (RingHom.mem_ker.2 h)
  let φ : P.asIdeal.ResidueField →+* κ := Ideal.ResidueField.lift P.asIdeal g le_rfl hunit
  have hcomp : φ.comp (algebraMap R P.asIdeal.ResidueField) = g :=
    RingHom.ext fun r => Ideal.ResidueField.lift_algebraMap _ _ le_rfl hunit r
  letI : Algebra P.asIdeal.ResidueField κ := φ.toAlgebra
  obtain ⟨e⟩ := FieldChangeInter.nonempty_homology_equiv κ
    (((ModuleCat.extendScalars (algebraMap R P.asIdeal.ResidueField)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K) q
  have e2 := ((HomologicalComplex.homologyFunctor _ _ q).mapIso
    ((Functor.mapHomologicalComplexCompIso
      (ModuleCat.extendScalarsComp (algebraMap R P.asIdeal.ResidueField) φ).symm
        (ComplexShape.up ℕ)).app K)).toLinearEquiv
  have e3 : (↑((((ModuleCat.extendScalars (φ.comp (algebraMap R P.asIdeal.ResidueField))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology q) : Type) =
      (↑((((ModuleCat.extendScalars g).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology q) : Type) := by rw [hcomp]
  rw [← Module.finrank_baseChange (R := κ), Module.finrank_zero_iff]
  exact (((Equiv.cast e3).symm.trans e2.symm.toEquiv).trans e.toEquiv).subsingleton_congr

theorem subsingleton_coh_pull_of_ker_le : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0})
    (f : X ⟶ Sp R) [IsProper f] [Flat f] (M : LB X), M.IsLB → ∀ (κ₁ κ₂ : Type) [Field κ₁] [Field κ₂]
    (g₁ : R →+* κ₁) (g₂ : R →+* κ₂) (X₁ X₂ : Scheme.{0}) (f₁ : X₁ ⟶ Sp κ₁) (f₂ : X₂ ⟶ Sp κ₂) (π₁ : X₁ ⟶ X)
    (π₂ : X₂ ⟶ X), IsPullback π₁ f₁ f (spMap g₁) → IsPullback π₂ f₂ f (spMap g₂) →
    RingHom.ker g₂ ≤ RingHom.ker g₁ → ∀ q : ℕ, Subsingleton (coh (LB.toMod (M.pull π₁)) q) →
    Subsingleton (coh (LB.toMod (M.pull π₂)) q) := by
  intro R _ _ X f _ _ M hM κ₁ κ₂ _ _ g₁ g₂ X₁ X₂ f₁ f₂ π₁ π₂ h₁ h₂ hker q hsub
  haveI : CompactSpace X := by
    have : QuasiCompact f := inferInstance
    exact ⟨(QuasiCompact.isCompact_preimage (f := f) _ isOpen_univ isCompact_univ)⟩
  obtain ⟨ι, _, U, hU, hUtop⟩ :=
    GlobalTheory.QCoh.exists_finite_affine_cover_of_isCompact (X := X) (W := ⊤) isCompact_univ
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hsep : X.IsSeparated := by
    have e : terminal.from X = f ≫ terminal.from _ := terminal.hom_ext _ _
    exact ⟨by rw [e]; infer_instance⟩
  have hint : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) :=
    (GlobalTheory.cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).1 (Or.inl hsep) ι U hU
  have hcov : ⨆ i, U i = ⊤ := hUtop.symm
  haveI : IsAffineHom π₁ := MorphismProperty.of_isPullback h₁.flip inferInstance
  haveI : IsAffineHom π₂ := MorphismProperty.of_isPullback h₂.flip inferInstance
  obtain ⟨hc₁, hi₁⟩ := affine_cover_preimage_of_isAffineHom π₁ U hcov hint
  obtain ⟨hc₂, hi₂⟩ := affine_cover_preimage_of_isAffineHom π₂ U hcov hint
  haveI : SheafOfModules.IsQuasicoherent (LB.toMod M) := GlobalTheory.LB.isQuasicoherent_toMod hM
  haveI : IsFiniteQC (LB.toMod M) :=
    GlobalTheory.QCoh.isFiniteQC_iff_isFiniteType.2 ⟨inferInstance, GlobalTheory.LB.isFiniteType_toMod hM⟩
  have hfin : ∀ p : ℕ, Module.Finite R ((cechLB f M U).homology p) := by
    intro p
    letI : Algebra R Γ(X, ⊤) := algebraΓOfHom f
    have e := ((HomologicalComplex.homologyFunctor _ _ p).mapIso
      (FieldChangeInter.cechIso f M U)).toLinearEquiv.trans (cechHEquivCoh R hcov hint (LB.toMod M) p)
    haveI := GlobalTheory.ProperFinite.finite_coh_of_isProper f (LB.toMod M) p
    exact Module.Finite.equiv e.symm
  obtain ⟨K, φ, hKz, hKfin, -, hKproj, -, -, hKq⟩ :=
    exists_finite_projective_complex_quasiIso (cechLB f M U) (Fintype.card ι)
      (fun p hp => GlobalTheory.AbLaw.isZero_cechLB_X f M U hp.le)
      (fun p => GlobalTheory.AbLaw.flat_cechLB_X f hM hint p) hfin
  haveI : ∀ i, Module.Finite R (K.X i) := hKfin
  haveI : ∀ i, Module.Projective R (K.X i) := hKproj
  have hsemi := GlobalTheory.semicontinuity_finite_projective_complex K (Fintype.card ι) hKz
  have hV := fun p => hsemi.1 q p
  have hus := hsemi.2.1 q
  have step : ∀ {κ : Type} [Field κ] (g : R →+* κ) (Y : Scheme.{0}) (fY : Y ⟶ Sp κ) (π : Y ⟶ X),
      IsPullback π fY f (spMap g) → (⨆ i, π ⁻¹ᵁ U i = ⊤) →
      (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, π ⁻¹ᵁ U i)) →
      (Subsingleton (coh (LB.toMod (M.pull π)) q) ↔
        Subsingleton ((((ModuleCat.extendScalars g).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology q)) := by
    intro κ _ g Y fY π h hc hi
    obtain ⟨e1⟩ := nonempty_cechLB_homology_equiv_coh fY (LB.isLB_pull hM π) hc hi q
    have e2 := (HomologicalComplex.homologyFunctor _ _ q).mapIso
      (GlobalTheory.AbLaw.cechLBBaseChangeIso hM h hint)
    letI : Algebra R κ := g.toAlgebra
    haveI : QuasiIso (((ModuleCat.extendScalars g).mapHomologicalComplex
      (ComplexShape.up ℕ)).map φ) := hKq κ
    have e3 := asIso (HomologicalComplex.homologyMap (((ModuleCat.extendScalars g).mapHomologicalComplex
      (ComplexShape.up ℕ)).map φ) q)
    exact ((e3.toLinearEquiv.toEquiv.trans e2.toLinearEquiv.toEquiv).trans e1).subsingleton_congr.symm
  have k1 := (fibre_lemma_2 K q hV g₁).1 ((step g₁ X₁ f₁ π₁ h₁ hc₁ hi₁).1 hsub)
  refine (step g₂ X₂ f₂ π₂ h₂ hc₂ hi₂).2 ((fibre_lemma_2 K q hV g₂).2 ?_)
  have hspec : (⟨RingHom.ker g₂, RingHom.ker_isPrime g₂⟩ : PrimeSpectrum R) ⤳
      (⟨RingHom.ker g₁, RingHom.ker_isPrime g₁⟩ : PrimeSpectrum R) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 hker
  have h0 : (fun p : PrimeSpectrum R => Module.finrank p.asIdeal.ResidueField
      ↑((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology q)) ⟨RingHom.ker g₁, RingHom.ker_isPrime g₁⟩ < 1 := by
    simp only [k1]; exact Nat.zero_lt_one
  have hlt := ((hus _ 1 h0).filter_mono hspec.nhds_le_nhds).self_of_nhds
  exact Nat.lt_one_iff.1 hlt

end GlobalTheory.SemicontLB
