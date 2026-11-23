import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

attribute [local instance] RingHom.ker_isPrime PrimeSpectrum.isPrime

noncomputable section

namespace GlobalTheory.FibreVanishGen

theorem primeCompl_ker_le {R : Type} [CommRing R] {κ : Type} [Field κ] (g : R →+* κ) :
    (RingHom.ker g).primeCompl ≤ Submonoid.comap g (IsUnit.submonoid κ) := by
  intro r hr
  rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
  exact isUnit_iff_ne_zero.2 fun h => (Ideal.mem_primeCompl_iff.1 hr) (RingHom.mem_ker.2 h)

def liftRes {R : Type} [CommRing R] {κ : Type} [Field κ] (g : R →+* κ) :
    (RingHom.ker g).ResidueField →+* κ :=
  Ideal.ResidueField.lift (RingHom.ker g) g le_rfl (primeCompl_ker_le g)

theorem liftRes_comp {R : Type} [CommRing R] {κ : Type} [Field κ] (g : R →+* κ) :
    (liftRes g).comp (algebraMap R (RingHom.ker g).ResidueField) = g :=
  RingHom.ext fun r => Ideal.ResidueField.lift_algebraMap _ _ le_rfl (primeCompl_ker_le g) r

theorem subsingleton_homology_iff {R : Type} [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ)
    {κ : Type} [Field κ] (g : R →+* κ) (q : ℕ) :
    Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).obj K).homology q) ↔
    Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0}
      (algebraMap R (RingHom.ker g).ResidueField)).mapHomologicalComplex _).obj K).homology q) := by
  set L := (RingHom.ker g).ResidueField
  set a := algebraMap R L
  letI : Algebra L κ := (liftRes g).toAlgebra
  let K' := ((ModuleCat.extendScalars.{0, 0, 0} a).mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  obtain ⟨e⟩ := FieldChangeInter.nonempty_homology_equiv (R := L) κ K' q
  have e₁ : ModuleCat.extendScalars.{0, 0, 0} g ≅
      ModuleCat.extendScalars.{0, 0, 0} a ⋙ ModuleCat.extendScalars.{0, 0, 0} (algebraMap L κ) :=
    eqToIso (congrArg _ (liftRes_comp g).symm) ≪≫ ModuleCat.extendScalarsComp a (liftRes g)
  have e₂ : ((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅
      ((ModuleCat.extendScalars.{0, 0, 0} (algebraMap L κ)).mapHomologicalComplex _).obj K' :=
    (NatIso.mapHomologicalComplex e₁ _).app K ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm.app K)
  have e₃ := ((HomologicalComplex.homologyFunctor _ _ q).mapIso e₂).toLinearEquiv
  refine Iff.trans (e₃.toEquiv.trans e.toEquiv).subsingleton_congr ?_
  constructor
  · intro h
    by_contra hV
    rw [not_subsingleton_iff_nontrivial] at hV
    exact not_nontrivial_iff_subsingleton.2 h (Module.FaithfullyFlat.lTensor_nontrivial L κ _)
  · intro h
    infer_instance

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ), (∀ p, n < p → IsZero (C.X p)) → (∀ p, Module.Flat R (C.X p)) → (∀ p, Module.Finite R (C.homology p)) → ∀ (κ₁ κ₂ : Type) [Field κ₁] [Field κ₂] (g₁ : R →+* κ₁) (g₂ : R →+* κ₂), RingHom.ker g₂ ≤ RingHom.ker g₁ → ∀ q : ℕ, Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0} g₁).mapHomologicalComplex _).obj C).homology q) → Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0} g₂).mapHomologicalComplex _).obj C).homology q) := by
  intro R _ _ C n hn hflat hfin κ₁ κ₂ _ _ g₁ g₂ hle q h1
  obtain ⟨K, φ, hKn, hKfin, -, hKproj, -, -, hext⟩ :=
    exists_finite_projective_complex_quasiIso C n hn hflat hfin
  have tr : ∀ (κ : Type) [Field κ] (g : R →+* κ),
      Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).obj C).homology q) ↔
      Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).obj K).homology q) := by
    intro κ _ g
    letI := g.toAlgebra
    haveI := hext κ
    exact (asIso (HomologicalComplex.homologyMap
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R κ)).mapHomologicalComplex _).map φ) q)
      ).toLinearEquiv.toEquiv.subsingleton_congr.symm
  haveI := hKfin
  haveI := hKproj
  obtain ⟨hfinH, hsc, -⟩ := semicontinuity_finite_projective_complex K n hKn
  let P₁ : PrimeSpectrum R := ⟨RingHom.ker g₁, RingHom.ker_isPrime g₁⟩
  let P₂ : PrimeSpectrum R := ⟨RingHom.ker g₂, RingHom.ker_isPrime g₂⟩
  have h1' := (subsingleton_homology_iff K g₁ q).1 ((tr κ₁ g₁).1 h1)
  have hP₁ : Module.finrank P₁.asIdeal.ResidueField ((((ModuleCat.extendScalars
      (algebraMap R P₁.asIdeal.ResidueField)).mapHomologicalComplex _).obj K).homology q) < 1 := by
    rw [Module.finrank_zero_of_subsingleton]
    exact zero_lt_one
  have hsp : P₂ ⤳ P₁ := (PrimeSpectrum.le_iff_specializes P₂ P₁).1 hle
  have hP₂ := ((hsc q P₁ 1 hP₁).filter_mono (specializes_iff_nhds.1 hsp)).self_of_nhds
  haveI := hfinH q P₂
  have h2' : Subsingleton ((((ModuleCat.extendScalars
      (algebraMap R P₂.asIdeal.ResidueField)).mapHomologicalComplex _).obj K).homology q) :=
    Module.finrank_zero_iff.1 (Nat.lt_one_iff.1 hP₂)
  exact (tr κ₂ g₂).2 ((subsingleton_homology_iff K g₂ q).2 h2')

end GlobalTheory.FibreVanishGen
