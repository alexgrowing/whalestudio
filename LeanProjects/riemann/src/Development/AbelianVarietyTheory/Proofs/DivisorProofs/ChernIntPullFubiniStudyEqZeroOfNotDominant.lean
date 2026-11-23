import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeFderivLtOfNotDominantChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothProjVarietyCompactManifoldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory

theorem chernInt_pull_fubiniStudy_eq_zero_of_not_dominant : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim) (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str), (∃ x : PSpace ℂ Y.dim, ¬ π (genericPoint Y.X) ⤳ x) → Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ (fun _ => 1) = 0 := by
  intro Y π hπ ⟨x, hx⟩
  have := ProjSpace.isIntegral_of_isDomain ℂ Y.dim
  obtain ⟨-, -, -, A', hA'⟩ := GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold Y
  have hA : IsAlgAtlas (ProjAn.finAtlas ℂ (RingHom.id ℂ) Y.dim) := AnRead.isAlgAtlas_finAtlas _
  have hne : π (genericPoint Y.X) ≠ genericPoint (PSpace ℂ Y.dim) := fun h =>
    hx (h ▸ genericPoint_specializes x)
  have hc := (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf (RingHom.id ℂ)
  have hs := (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).isSmooth hA.anRead
  rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y _ _ (hc.pull π hπ)).2 A' hA',
    SameForm.mInt_eq (fun _ => hs.sameForm_pull hA hA' π hπ)]
  exact rankDrop _ A' _ (hA.holoMap hA' (f := π) fun _ => rfl)
    (GlobalTheory.T.finrank_range_fderiv_lt_of_not_dominant_charts ℂ _ _ _ _ _ _ _ A' hA hA' π hπ hne) _ (fun _ => hs.isPotential hA) _

end GlobalTheory
