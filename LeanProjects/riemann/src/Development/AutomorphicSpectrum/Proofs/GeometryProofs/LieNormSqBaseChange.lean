import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem lieNormSq_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (ω : R) (ω' : R') (C : Ell H R ω) (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) (σ : R' →+* ℂ) (r : ℝ), EllMap C' C f φ → (IsLieNormSq C.P C.v (σ.comp f) r ↔ IsLieNormSq C'.P C'.v σ r) := by
  intro E _ _ _ H R R' _ _ ω ω' C C' f φ σ r h
  exact (GlobalTheory.CM.EllComp.isLieNormSq_iff h.2.1 h.2.2.1 σ r).symm

end GlobalTheory.CompanionTheory.Ar.Fl
