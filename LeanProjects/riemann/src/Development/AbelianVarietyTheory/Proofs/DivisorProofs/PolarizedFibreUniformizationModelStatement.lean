import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedFibreUniformizationModel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_fibre_uniformization_model : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp K)) (AA : Over (Sp (𝓞 K))) [GrpObj AA] [IsCommMonObj AA] (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (N : ℕ) (w : LB.Iso (MM.L.pull φ) (lbPow P.L N)) (σ : K →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψσ : Q.A.left ⟶ P.A.left) (wσ : LB.Iso ((lbPow P.L N).pull ψσ) (lbPow Q.L N)) (g : ℕ) (u : HolUnif Q.A Q.L g), GlobalTheory.MBModel.IsModel w → GlobalTheory.IsPolFibre σ P Q ψσ → wσ.IsGen → ∃ ρ' : ℂ, GlobalTheory.MBModel.RigIs w σ wσ u ρ' ∧ ρ' ≠ 0 := by
  first | exact @GlobalTheory.MBModel.exists_rigIs_ne_zero | exact GlobalTheory.MBModel.exists_rigIs_ne_zero | (intros; apply GlobalTheory.MBModel.exists_rigIs_ne_zero <;> assumption)
