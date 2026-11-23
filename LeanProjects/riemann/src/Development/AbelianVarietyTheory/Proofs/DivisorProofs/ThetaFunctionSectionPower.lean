import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowEqThetaLevelChar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

namespace GlobalTheory

theorem exists_isFnPow_isThetaFn_of_isAH :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → u.IsAH Hm χ → ∀ (N : ℕ) (s : (lbPow L N).Sec), ∃ θ : (Fin g → ℂ) → ℂ, u.IsFnPow N s θ ∧ u.IsThetaFn Hm χ N θ := by
  intro A _ L g u Hm χ hL hAH N s
  obtain ⟨θ, hd, hfn, -, hper⟩ := GlobalTheory.ThetaBundleSec.exists_fn u hL N s
  refine ⟨θ, hfn, hd, fun l z => hper z (z + l) _ ?_ fun i hi => hAH.2.2.2 l i z hi⟩
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

end GlobalTheory
