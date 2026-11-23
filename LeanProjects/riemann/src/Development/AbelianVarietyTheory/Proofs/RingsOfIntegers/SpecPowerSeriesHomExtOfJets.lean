import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetFramesDifferByUnitEachOrder
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransUnit

theorem hom_ext_of_jets : ∀ (V : Type) [CommRing V] [IsLocalRing V] (κ : Type) [Fintype κ] [DecidableEq κ] (Y : Scheme.{0}) (f g : Sp (MvPowerSeries κ V) ⟶ Y), (∀ m, spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ f = spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ g) → f = g := by
  intro V _ _ κ _ _ Y f g h
  have hs : Function.Surjective (jetA (V := V) κ 0 : MvPowerSeries κ V →+* Jet V κ 0) :=
    fun a => GlobalTheory.ChartCmp.FrameRatio.psJet_surj 0 a
  have hn : Nontrivial (Jet V κ 0) :=
    (Formalism.L2.Pj.jetAug : Jet V κ 0 →ₐ[V] V).toRingHom.domain_nontrivial
  have hl : IsLocalRing (Jet V κ 0) := IsLocalRing.of_surjective' _ hs
  have hc : spMap (jetA (V := V) κ 0 : MvPowerSeries κ V →+* Jet V κ 0) (closedPoint (Jet V κ 0)) =
      closedPoint (MvPowerSeries κ V) := by
    have : IsLocalHom (CommRingCat.ofHom (jetA (V := V) κ 0 : MvPowerSeries κ V →+* Jet V κ 0)).hom :=
      IsLocalHom.of_surjective _ hs
    exact Spec_closedPoint
  have hx : g (closedPoint (MvPowerSeries κ V)) = f (closedPoint (MvPowerSeries κ V)) := by
    rw [← hc]
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans (Eq.trans ?_ (Scheme.Hom.comp_apply _ _ _))
    rw [h]
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.existsUnique_factor_stalk f rfl
  obtain ⟨φ', hφ', -⟩ := GlobalTheory.existsUnique_factor_stalk g hx
  have : φ = φ' := by
    ext1
    refine RingHom.ext fun b => GlobalTheory.FrameBiextId.ps_ext fun m => ?_
    have h1 : spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ Spec.map φ =
        spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ Spec.map φ' := by
      rw [← cancel_mono (Y.fromSpecStalk _), Category.assoc, Category.assoc, hφ, hφ', h]
    rw [← Spec.map_comp, ← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom b)
  rw [← hφ', ← this, hφ]

end GlobalTheory.TransUnit
