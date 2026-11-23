import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCovered
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPointEqOfIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleCanonicalTrivialLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadFromLocalizationStatement

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PolNormal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_generic_pull {S T : Type} [CommRing S] [IsDomain S] [CommRing T] [IsDomain T] (i : S →+* T)
    (hi : Function.Injective i) {t : SAB H (Sp S)} {t' : SAB H (Sp T)} (m : SABMap t' t (spMap i))
    (hg : GlobalTheory.LN.PolAt t (Out.jK S)) : GlobalTheory.LN.PolAt t' (Out.jK T) := by
  let ι : FractionRing S →+* FractionRing T :=
    IsLocalization.map (FractionRing T) i (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective i hi)
  refine GlobalTheory.DatUniq.polAt_pull m hg (Out.jK T) (spMap ι) ?_
  simp only [spMap, Out.jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact IsLocalization.map_comp _

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem relAmple_kTriv_of_normal {S : Type} [CommRing S] [IsDomain S] [CharZero S] [IsNoetherianRing S]
    (hS : IsIntegrallyClosed S) (t : SAB H (Sp S)) (hp : IsProper t.G.hom) (hg : GlobalTheory.LN.PolAt t (Out.jK S)) :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  have key : ∀ q : PrimeSpectrum S, ∃ (tO : SAB H (Sp (Localization.AtPrime q.asIdeal)))
      (_ : SABMap tO t (spMap (algebraMap S (Localization.AtPrime q.asIdeal)))),
      Out.RelAmple tO.G tO.PP.L ∧ Out.KTriv tO.G tO.PP.L := by
    intro q
    let O := Localization.AtPrime q.asIdeal
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap S O)) t
    refine ⟨_, m, ?_⟩
    have hi : Function.Injective (algebraMap S O) :=
      IsLocalization.injective O q.asIdeal.primeCompl_le_nonZeroDivisors
    have : CharZero O := charZero_of_injective_algebraMap hi
    have hO : IsIntegrallyClosed O :=
      isIntegrallyClosed_of_isLocalization O q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
    exact GlobalTheory.T.relative_ample_canonical_trivial_local E H O hO _ (MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp)
      (polAt_generic_pull _ hi m hg)
  have hA : Out.RelAmple t.G t.PP.L := by
    have := t.semi.quasiCompact
    have := t.semi.separated
    refine GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S) t.G t.PP.L t.PP.isLB inferInstance inferInstance fun s => ?_
    obtain ⟨tO, m, hA, -⟩ := key s
    obtain ⟨w, hw, -⟩ := m.lin
    exact GlobalTheory.T.relative_ample_spread_from_localization S s t.G t.PP.L hp t.PP.isLB tO.G m.φ tO.PP.L m.cart.1 tO.PP.isLB ⟨w, hw⟩ hA
  refine ⟨hA, GlobalTheory.KTrivGlob.kTriv_of_forall_point GlobalTheory.allSixLaws.1 E H (Sp S) t hp hA fun q => ?_⟩
  obtain ⟨tO, m, -, hK⟩ := key q
  have : q.asIdeal.IsPrime := q.isPrime
  exact ⟨_, _, tO, m, ⟨IsLocalRing.closedPoint _, PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal⟩, hK⟩

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal

end GlobalTheory.PolNormal
