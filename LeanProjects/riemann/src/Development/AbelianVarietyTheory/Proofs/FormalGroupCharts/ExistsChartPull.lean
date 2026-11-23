import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetSubPf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NuAlgLeOfCharts
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsoIntegralModelsMatchingLieBases
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionBaseChange
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFramesCoefficientRingBaseChange
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFrameGCoefficientRingBaseChange
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CubeFramesMoveToPullbackTriple
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionIffPullback
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameFirstPartialLawIffPullback
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSecondPartialLawIffPullback
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSymmetryIffPullback
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointSeriesFramesPullback
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNMap
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsCanonGaugeMapFB
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsRawChartBaseChangeJetPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.DepthExt

theorem vV_unit {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {u : V} (hu : IsUnit u) : vV V (algebraMap V K u) = 0 := by
  have h : valV V (algebraMap V K u) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal u).1 h hu
  simp [vV, h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem grp_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 _) (𝟙 _) :=
  ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun _ x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
      (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm⟩

section Tangent
variable {V V' : Type} [CommRing V] [CommRing V']

theorem comb_iff (t : SAB H (Sp V)) {m : ℕ} (v : Fin m → (epsR V ⟶ t.G)) (cf : Fin m → V) (w : epsR V ⟶ t.G) :
    IsLieComb cf v w ↔ IsCombAtG t (𝟙 _) (fun i => (v i).left) cf w.left := by
  simp only [Chart.comb_push (grp_id t.G), Category.comp_id]
  exact Iff.rfl

theorem tan_iff (t : SAB H (Sp V)) (w : epsR V ⟶ t.G) : IsTangent w ↔ IsTanAtG t (𝟙 _) w.left := by
  simp only [Chart.tan_push (grp_id t.G), Category.comp_id]
  exact ⟨fun h => ⟨(Over.w w).trans (Category.comp_id _).symm, h⟩, fun h => h.2⟩

variable (ψ : V →+* V') {t : SAB H (Sp V)} {t' : SAB H (Sp V')} (mp : SABMap t' t (spMap ψ))

theorem exists_lift {A A' : Type} [CommRing A] [CommRing A'] [Algebra V A] [Algebra V' A'] (g : A →+* A')
    (hg : g.comp (algebraMap V A) = (algebraMap V' A').comp ψ) (x : Sp A ⟶ t.G.left)
    (hx : x ≫ t.G.hom = spMap (algebraMap V A)) :
    ∃ x' : Sp A' ⟶ t'.G.left, x' ≫ mp.φ = spMap g ≫ x ∧ x' ≫ t'.G.hom = spMap (algebraMap V' A') :=
  ⟨mp.cart.1.lift (spMap g ≫ x) (spMap (algebraMap V' A')) (by
    rw [Category.assoc, hx, RawChartBC.spMap_spMap, RawChartBC.spMap_spMap, hg]),
    mp.cart.1.lift_fst _ _ _, mp.cart.1.lift_snd _ _ _⟩

end Tangent

theorem map_sq {V K V' K' σ : Type} [CommRing V] [CommRing K] [CommRing V'] [CommRing K'] {f : V →+* K}
    {f' : V' →+* K'} {φ : K →+* K'} {ψ : V →+* V'} (h : ∀ a, f' (ψ a) = φ (f a)) {g : MvPowerSeries σ V}
    {g' : MvPowerSeries σ K} (hg : g' = MvPowerSeries.map f g) :
    MvPowerSeries.map f' (MvPowerSeries.map ψ g) =
      MvPowerSeries.map (algebraMap K' K') (MvPowerSeries.map φ g') := by
  ext m
  simp [hg, MvPowerSeries.coeff_map, h]

end GlobalTheory.DepthExt
