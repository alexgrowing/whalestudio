import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliIsReduced
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem moduli_twist_phi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (g : HostAut H) (a : TwIso D g) (h : TwOK Xo.univ g a),
    ∃ Φ : Xo.X ⟶ Xo.X, Φ ≫ Xo.s = Xo.s ∧ Nonempty (ObjMap (twistObj Xo.univ g a h) Xo.univ Φ) := by
  intro E _ _ _ H D l Xo g a h
  obtain ⟨f, ⟨hf, ho⟩, -⟩ :=
    Xo.rep Xo.X Xo.s (moduli_isReduced E H D l Xo) (twistObj Xo.univ g a h)
  exact ⟨f, hf, ho⟩

end GlobalTheory.CompanionTheory.Ar
