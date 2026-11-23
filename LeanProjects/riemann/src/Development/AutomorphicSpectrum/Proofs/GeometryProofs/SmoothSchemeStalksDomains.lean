import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem isDomain_and_isIntegrallyClosed_stalk_sp_field (K : Type) [Field K] (y : Sp K) :
    IsDomain ((Sp K).presheaf.stalk y) ∧ IsIntegrallyClosed ((Sp K).presheaf.stalk y) := by
  let p : PrimeSpectrum K := y
  have hle : p.asIdeal.primeCompl ≤ IsUnit.submonoid K := fun x hx =>
    isUnit_iff_ne_zero.2 fun h0 => hx (h0 ▸ p.asIdeal.zero_mem)
  let e₁ : K ≃+* Localization.AtPrime p.asIdeal :=
    (IsLocalization.atUnits K p.asIdeal.primeCompl hle).toRingEquiv
  let e₂ : (Sp K).presheaf.stalk y ≃+* Localization.AtPrime p.asIdeal :=
    (AlgebraicGeometry.Spec.stalkIso (CommRingCat.of K) p).commRingCatIsoToRingEquiv
  let e : K ≃+* (Sp K).presheaf.stalk y := e₁.trans e₂.symm
  haveI := Field.instIsIntegrallyClosed K
  exact ⟨(MulEquiv.isField (Field.toIsField K) e.symm.toMulEquiv).isDomain, IsIntegrallyClosed.of_equiv e⟩

theorem isDomain_stalk_of_smoothOfRelativeDimension_field (K : Type) [Field K] (e : ℕ)
    (X : Scheme.{0}) (g : X ⟶ Sp K) (hg : SmoothOfRelativeDimension e g) (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  haveI : Smooth g := SmoothOfRelativeDimension.smooth e g
  exact (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g
    (isDomain_and_isIntegrallyClosed_stalk_sp_field K) x).1

end GlobalTheory.CompanionTheory.Ar.SncBase
