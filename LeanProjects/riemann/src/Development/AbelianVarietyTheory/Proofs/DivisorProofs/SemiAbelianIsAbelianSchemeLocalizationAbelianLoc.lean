import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRestrictOfSubsetAbLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusAtPrime

theorem isAbelianScheme_localization : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (p : Sp R) [p.asIdeal.IsPrime], p ∈ abLocus G₁ → IsAbelianScheme ((Over.pullback (spMap (algebraMap R (Localization.AtPrime p.asIdeal)))).obj G₁) := by
  intro R _ _ _ G₁ _ _ hG p _ hp
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsDomain (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isDomain_localization p.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  set f := spMap (algebraMap R (Localization.AtPrime p.asIdeal)) with hf
  have hG' : IsSemiAbelian ((Over.pullback f).obj G₁) := IsSemiAbelian.pullback f G₁ hG
  have hopen : IsOpen (abLocus G₁) := GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian G₁ hG
  have hgen : ∀ z : Sp (Localization.AtPrime p.asIdeal), f z ∈ abLocus G₁ := by
    intro z
    have hle : (f z) ⤳ p := by
      refine (PrimeSpectrum.le_iff_specializes (R := R) (f z) p).1 ?_
      have hr : (f z : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal))) := by
        exact ⟨z, rfl⟩
      rw [PrimeSpectrum.localization_comap_range (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl] at hr
      show (f z : PrimeSpectrum R).asIdeal ≤ (p : PrimeSpectrum R).asIdeal
      intro x hx
      by_contra hxp
      exact Set.disjoint_left.1 hr hxp hx
    exact hle.mem_open hopen hp
  have hab : abLocus ((Over.pullback f).obj G₁) = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G₁.hom f) z).1 (hgen z)
  exact
    { comm := hG'.comm
      smooth := hG'.smooth
      proper := GlobalTheory.AbLocusProperNormal.isProper_of_abLocus_eq_univ _ _ hG' hab
      geomConnected := hG'.geomConnected }

end GlobalTheory.AbLocusAtPrime
