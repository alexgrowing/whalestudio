import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
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

namespace GlobalTheory.ArchLim

theorem chernMat_pull_cell : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (σ : k →+* ℂ) (c : AlgChart q σ n) (c' : AlgChart p σ D), IsCell ε π w c c' → ∀ (N : HermLB q), ∀ y' ∈ c'.e.source, chernMat ((N.pull π w).φ σ) c' y' = cHess D (fun v => ((N.φ σ).φ (pick (N.φ σ).isLB (PtsOver.map π w (spMap σ) y')) (c.e.symm (base ε v)) : ℂ)) (c'.e y') := by
  intro k _ B Y q p π w n r D ε σ c c' hc N y hy
  obtain ⟨hs, -, hb⟩ := hc
  have hi : y ∈ ptsIn p σ ((N.pull π w).B.U fun _ => pick (N.φ σ).isLB (PtsOver.map π w (spMap σ) y)) := by
    intro x hx
    exact Set.mem_iInter.2 fun _ => mem_pick (N.φ σ).isLB (PtsOver.map π w (spMap σ) y) hx
  rw [chernMat, c'.hess_eq ((N.pull π w).cInf σ) hy hi (mem_pick _ y)]
  refine ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_
  filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hy)] with v hv
  have h₁ := c'.e.map_target hv
  have h₂ := hb _ h₁
  rw [c'.e.right_inv hv] at h₂
  have h₃ : PtsOver.map π w (spMap σ) (c'.e.symm v) ∈ c.e.source := (hs ▸ h₁).1
  rw [h₂, c.e.left_inv h₃]
  exact congrArg _ (Weight.pull_φ (N.φ σ) π w _ (c'.e.symm v))

end GlobalTheory.ArchLim
