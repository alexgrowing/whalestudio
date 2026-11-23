import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatricesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMapStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameRingOverTestRingStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in

theorem _root_.GlobalTheory.Frames.exists_univFrame_testRing : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (p : _root_.Formalism.L2.Pj.TRing c.F) (y₀ : _root_.Formalism.L2.Pj.FrPt Xo c p.R),
    ∃ (A : _root_.Formalism.L2.Pj.TRing c.F) (π : p.R →ₐ[c.F] A.R)
      (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R)) (s : (A.R)ˣ)
      (u : _root_.Formalism.L2.Pj.FrPt Xo c A.R), _root_.GlobalTheory.Frames.UnivFrame y₀ π X s u := by
  intro hbc E _ _ _ H Dw l Xo c p y₀
  obtain ⟨A, π, X, s, h⟩ := _root_.GlobalTheory.exists_frameRing_testRing c.F (E →+* ℂ) Dw.mult p
  obtain ⟨u₀, hu₀⟩ := _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hbc E H Dw l Xo c p.R A.R π y₀
  obtain ⟨u, hu, -⟩ := _root_.GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A.R u₀ X s h.1
  exact ⟨A, π, X, s, u, h, u₀, hu₀, hu⟩

end GlobalTheory.Frames
