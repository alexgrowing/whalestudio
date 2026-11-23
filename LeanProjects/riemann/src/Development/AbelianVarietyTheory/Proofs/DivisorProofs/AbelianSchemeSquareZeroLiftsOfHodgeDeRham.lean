import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFlatPullbackReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDeRhamHomologySummandsCrystalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationDirectSummandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftSystemOfSummandReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftSystemHomOfFiltrationEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftEqComapSystemFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchemePresentingSquareZeroSmoothLiftSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodForSquareZeroLiftClassificationOfAbelianScheStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismLiftSystemPresentsOfHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationInfEqAndFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothLiftOfSquareZeroLiftSystemPresentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftReductionStandardFactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePresentedBySystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCrystalReducesToDeRhamSqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroSmoothLiftSystemPresentsStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem abelianSchemeLifts_of_hodgeDeRham (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) :
    AbelianSchemeLifts := by
  intro R _ _ I hI R₀ _ π hπ hk g A₀ _ A' _ i' h' hA hg
  haveI : IsNoetherianRing R₀ := isNoetherianRing_of_surjective R R₀ π hπ
  obtain ⟨-, -, -, -, -, -, hA₀, hg₀⟩ := GlobalTheory.T.abelianLift_reduction_standard_facts hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  have hG : Good A₀.hom := GlobalTheory.T.goodForSquareZeroLiftClassification_of_abelianScheme hC hH R₀ A₀ g hA₀ hg₀
  have hR : RhoBC hI hk A₀.hom := GlobalTheory.T.abelianScheme_crystal_reduces_to_deRham_sqZero hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨ad1, ad2, ad3⟩ := GlobalTheory.T.admissible_deRhamHomology_summands_crystal hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨S', ⟨P'⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom A'.left A'.hom i' h'.1 hA.smooth
  obtain ⟨hF', hc'⟩ := GlobalTheory.T.abelian_scheme_presented_by_system hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg S' P'
  have core1 := GlobalTheory.T.squareZeroLiftSystem_filtration_direct_summand R R₀ I hI π hπ hk A₀.left A₀.hom hG hR S' hF' hc'
  have ksup := GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk A₀.left A₀.hom S' hR hF'
  have fil : ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)), Smooth X.hom →
      ∀ S : Sys I π A₀.hom, S.Presents X.hom i → schemeFil (divided₂ hI) A₀ X i h.w =
        ((S.K hI).comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator := fun X i h hX S P ↦
    congrArg Submodule.dualAnnihilator
      (GlobalTheory.T.primitiveCrystalHodgeLiftClasses_eq_comap_sys hC R R₀ I hI π hπ hk A₀ hA₀.proper hA₀.geomConnected X i h hX S P)
  refine ⟨⟨fun X i h hX ↦ ?_, fun F hF ↦ ?_⟩, fun X Y i j h k hX hY e ↦ ?_⟩
  · obtain ⟨S, ⟨P⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
    obtain ⟨hc, hs⟩ := core1 S
    obtain ⟨F, hF, e⟩ := ad1 (S.K hI) hc fun c ↦ by rw [hs]; exact ksup c
    exact ⟨F, hF, (fil X i h hX S P).trans e⟩
  · obtain ⟨K, hc, hs, e⟩ := ad2 F hF
    obtain ⟨S, rfl⟩ := GlobalTheory.T.exists_squareZeroLiftSystem_of_summand_reduction R R₀ I hI π hπ hk A₀.left A₀.hom hG hR S' hF' hc' K hc
      (Submodule.ext fun c ↦ (hs c).trans (ksup c).symm)
    obtain ⟨X, s, i, h1, h2, ⟨P⟩⟩ := GlobalTheory.T.exists_scheme_presenting_squareZeroSmoothLiftSystem R R₀ I hI π hπ hk A₀.left A₀.hom S
    obtain ⟨h, hX⟩ := GlobalTheory.T.isSmoothLift_of_squareZeroLiftSystemPresents R R₀ I hI π hπ hk A₀.left A₀.hom S X s i h1 h2 P
    exact ⟨Over.mk s, i, h, hX, (fil (Over.mk s) i h hX S P).trans e⟩
  · obtain ⟨S, ⟨P⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
    obtain ⟨T, ⟨Q⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom Y.left Y.hom j k hY
    have hK : T.K hI = S.K hI := ad3 _ _ (core1 T).1 (core1 S).1
      ((fil Y j k hY T Q).symm.trans (e.symm.trans (fil X i h hX S P)))
    have hT : T.Full hI := (GlobalTheory.T.squareZeroLiftSystem_filtration_inf_eq_and_full R R₀ I hI π hπ hk A₀.left A₀.hom hG.const S' T).2 hF'
    obtain ⟨f, hf, hij⟩ := GlobalTheory.T.exists_morphism_liftSystemPresents_of_hom R R₀ I hI π hπ hk A₀.left A₀.hom T S X.left X.hom i Y.left Y.hom j h Q P
      (GlobalTheory.T.exists_squareZeroLiftSystem_hom_of_filtration_eq R R₀ I hI π hπ hk A₀.left A₀.hom hG hR T S hT hK)
    haveI := hX
    have hn : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk]; exact hI⟩
    haveI : IsIso (Over.homMk f hf : X ⟶ Y) :=
      GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction R R₀ π hπ hn X Y A₀ A₀ i j h k inferInstance
        (Over.homMk f hf) (𝟙 A₀) (by simpa using hij) inferInstance
    exact ⟨asIso (Over.homMk f hf : X ⟶ Y), hij⟩

end GlobalTheory.LiftSys
