import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfIsIsoRestrictStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapBijectiveOfIsIsoRestrictStatement

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.BirModel

theorem exists_smooth_projective_model : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (s : Y ⟶ X) (_ : IsDominant s), SmoothOfRelativeDimension n (s ≫ p) ∧
      IsProjOver (s ≫ p) ∧ Function.Bijective (functionFieldMap s) := by
  intro hP k _ _ X _ p n hp hdim
  obtain ⟨Y, s, U, hY, hsm, hpr, hU, hiso⟩ := GlobalTheory.WeakRes.weak_resolution hP k X p n hp hdim
  have hdom : IsDominant s := GlobalTheory.T.isDominant_of_isIso_restrict' X Y s U hU hiso
  exact ⟨Y, hY, s, hdom, hsm, hpr, GlobalTheory.T.functionFieldMap_bijective_of_isIso_restrict' X Y s U hU hiso⟩

end GlobalTheory.BirModel
