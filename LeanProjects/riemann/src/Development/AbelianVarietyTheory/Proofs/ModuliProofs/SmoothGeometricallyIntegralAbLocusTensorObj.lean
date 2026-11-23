import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

theorem _root_.GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj : ∀ (X : Scheme.{0}) (P Q : Over X), Smooth P.hom → Smooth Q.hom → GeometricallyIntegral P.hom → GeometricallyIntegral Q.hom → Smooth (P ⊗ Q).hom ∧ GeometricallyIntegral (P ⊗ Q).hom ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus P ∩ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus Q ⊆ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus (P ⊗ Q) := by
  intro X P Q hPs hQs hPi hQi
  haveI := _root_.GlobalTheory.geometricallyConnected_of_geometricallyIntegral P.hom
  haveI := _root_.GlobalTheory.geometricallyConnected_of_geometricallyIntegral Q.hom
  refine ⟨_root_.GlobalTheory.smooth_tensorObj_hom P Q, _root_.GlobalTheory.geometricallyIntegral_tensorObj_hom P Q, ?_⟩
  intro s hs'
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus, Set.mem_inter_iff, Set.mem_setOf_eq] at hs' ⊢
  obtain ⟨hP, hQ⟩ := hs'
  intro K _ _ t hs
  haveI : IsProper ((Over.pullback t).obj P).hom := hP K t hs
  haveI : IsProper ((Over.pullback t).obj Q).hom := hQ K t hs
  haveI : IsIso (CartesianMonoidalCategory.prodComparison (Over.pullback t) P Q).left :=
    Functor.map_isIso (Over.forget (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K))
      (CartesianMonoidalCategory.prodComparison (Over.pullback t) P Q)
  have h : IsProper ((CartesianMonoidalCategory.prodComparison (Over.pullback t) P Q).left ≫
      ((Over.pullback t).obj P ⊗ (Over.pullback t).obj Q).hom) := by
    rw [Over.tensorObj_hom]; infer_instance
  rw [Over.w] at h
  exact h

end GlobalTheory
