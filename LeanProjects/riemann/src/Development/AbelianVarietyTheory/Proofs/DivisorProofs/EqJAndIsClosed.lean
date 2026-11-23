import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonRefinementModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopOfInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroResidueField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TrueGeo.ReadPts

theorem eq_j_and_isClosed : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P M : TrueGeo.Model Y) (π : P.X ⟶ M.X), P.j ≫ π = M.j → ∀ (y : Y.X) (x : P.X), IsAlgPt x → π x = M.j y → x = P.j y ∧ IsClosed ({y} : Set Y.X) := by
  intro F _ _ Y P M π hπ y x hx hxy
  obtain ⟨y', hy', rfl⟩ := GlobalTheory.TrueGeo.NefModel.exists_isClosed P hx
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  have : IsPreimmersion M.j := MorphismProperty.of_isPullback M.pb.flip this
  have h : M.j y' = M.j y := by
    rw [← hxy, ← hπ, Scheme.Hom.comp_apply]
  obtain rfl := M.j.isEmbedding.injective h
  exact ⟨rfl, hy'⟩

end GlobalTheory.TrueGeo.ReadPts
