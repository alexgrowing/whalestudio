import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnDiagValExtTrace

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

theorem VMetric.exists_isFlagCh2 : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    (p : X ⟶ Sp k) [IsIntegral X], IsRegSurf p → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r)
    (H : h.IsCInf) (fl : Vert.Flag E r), ∃ a : ℝ, VMetric.IsFlagCh2 H fl a := by
  intro HC k _ X p _ hX E r h H fl
  obtain ⟨⟨Φ, hΦ⟩, -⟩ := (HC.arExists k X p 1 hX.toIsArithVar).2 (Fin r) fun i => VMetric.grLB fl i H
  refine ⟨_, fun i => ?_, _, ((HC.arIso k X p 1 hX.toIsArithVar).2 _ _ Φ hΦ).1, rfl⟩
  exact VMetric.bcFinite_of_curve k X p hX.isProjOver (GlobalTheory.RegGenSmooth.genSmooth_of_isRegSurf k X p hX).1 _ _ _ _ _ _ _ (H.restrict _ _)

end GlobalTheory
