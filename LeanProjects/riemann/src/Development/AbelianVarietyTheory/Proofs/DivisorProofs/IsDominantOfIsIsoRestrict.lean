import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem isDominant_of_isIso_restrict (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X)
    (U : X.Opens) (hU : (U : Set X).Nonempty) (h : IsIso (s ∣_ U)) : IsDominant s := by
  refine ⟨?_⟩
  have hd : Dense (U : Set X) := U.isOpen.dense hU
  refine hd.mono ?_
  intro x hx
  obtain ⟨y, hy⟩ := (s ∣_ U).surjective ⟨x, hx⟩
  refine ⟨y.1, ?_⟩
  have := morphismRestrict_base_coe s U y
  rw [hy] at this
  exact this.symm

end GlobalTheory.Discrepancy
