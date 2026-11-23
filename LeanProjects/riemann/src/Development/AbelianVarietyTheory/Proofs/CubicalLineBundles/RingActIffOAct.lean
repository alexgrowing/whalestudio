import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj ComplexOrder in

theorem _root_.GlobalTheory.LamF.ringAct_iff_oAct :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G],
      (∀ a : _root_.ReciprocityTheory.ChartRestriction.G.Out.RingAct G O, ∃ b : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G, b.act = a.act) ∧
        ∀ b : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G, ∃ a : _root_.ReciprocityTheory.ChartRestriction.G.Out.RingAct G O, a.act = b.act := by
  intro O _ S G _ _
  exact ⟨fun a => ⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ofRingAct a, rfl⟩, fun b => ⟨b.toRingAct, rfl⟩⟩

end GlobalTheory.LamF
