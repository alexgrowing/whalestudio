import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

namespace GlobalTheory.CommonFrames

theorem exists_common_affine_frames : ∀ (X : Scheme.{0}) (M M' : X.Modules) (r : ℕ), IsVB M r → IsVB M' r → ∀ x : X, ∃ (V : X.Opens)
    (f : Fin r → Γ(M, V)) (f' : Fin r → Γ(M', V)), VB.IsFrame f ∧ VB.IsFrame f' ∧ IsAffineOpen V ∧ x ∈ V := by
  intro X M M' r h h' x
  obtain ⟨U, e, hx, he⟩ := h x
  obtain ⟨V, e', hV, hxV, hle, he'⟩ := IsVB.exists_affine h' hx
  exact ⟨V, fun i => Twist.resM M hle (e i), e', GlobalTheory.VB.IsFrame.res he hle, he', hV, hxV⟩

end GlobalTheory.CommonFrames
