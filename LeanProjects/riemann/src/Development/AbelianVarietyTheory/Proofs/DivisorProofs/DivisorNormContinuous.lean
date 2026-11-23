import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormStatementStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.IsDivNorm

theorem continuous : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} (R : AnRead p σ d) (C : Closeds Y) (n : CxPts p σ → ℝ), IsDivNorm R C n → Continuous n := by
  intro k _ Y p σ d R C n h
  refine continuous_iff_continuousAt.2 fun y => ?_
  obtain ⟨V, t, f, hy, -, hf, e⟩ := h.2 y
  have hc : ContinuousOn (fun z => ‖ev p σ V.1 t z‖ * Real.exp (-f z / 2)) (ptsIn p σ V.1) :=
    (continuousOn_ev _).norm.mul (((hf.continuousOn (isOpen_ptsIn _)).neg.div_const 2).rexp)
  refine (hc.congr fun z hz => ?_).continuousAt ((isOpen_ptsIn _).mem_nhds hy)
  refine (pow_left_inj₀ (h.1 z).1 (by positivity) two_ne_zero).1 ?_
  rw [e z hz, mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

end GlobalTheory.ShFam.IsDivNorm
