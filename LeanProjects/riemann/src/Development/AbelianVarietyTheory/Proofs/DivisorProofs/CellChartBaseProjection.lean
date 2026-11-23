import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDensityPushforwardIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNull
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

theorem cell_proj_and_image_eq : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (σ : k →+* ℂ) (c : AlgChart q σ n) (c' : AlgChart p σ D), IsCell ε π w c c' → (∀ v ∈ c'.e.target, PtsOver.map π w (spMap σ) (c'.e.symm v) = c.e.symm (base ε v)) ∧ ∀ A : Set (CxPts q σ), A ⊆ c.e.source → c'.e '' (PtsOver.map π w (spMap σ) ⁻¹' A ∩ c'.e.source) = base ε ⁻¹' (c.e '' A) := by
  intro k _ B Y q p π w n r D ε σ c c' h
  obtain ⟨h₁, h₂, h₃⟩ := h
  have first : ∀ v ∈ c'.e.target, PtsOver.map π w (spMap σ) (c'.e.symm v) = c.e.symm (base ε v) := by
    intro v hvt
    have hy := c'.e.map_target hvt
    have h₄ := h₃ _ hy
    rw [c'.e.right_inv hvt] at h₄
    have h₅ : PtsOver.map π w (spMap σ) (c'.e.symm v) ∈ c.e.source := (h₁ ▸ hy).1
    rw [h₄, c.e.left_inv h₅]
  refine ⟨first, fun A hA => ?_⟩
  ext v
  constructor
  · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
    exact ⟨_, hy, (h₃ y hy').symm⟩
  · rintro ⟨a, ha, hv⟩
    have hvt : v ∈ c'.e.target := by
      rw [h₂]
      change base ε v ∈ c.e.target
      rw [← hv]
      exact c.e.map_source (hA ha)
    refine ⟨c'.e.symm v, ⟨?_, c'.e.map_target hvt⟩, c'.e.right_inv hvt⟩
    change PtsOver.map π w (spMap σ) (c'.e.symm v) ∈ A
    rw [first v hvt, ← hv, c.e.left_inv (hA ha)]
    exact ha

end GlobalTheory.ArchLim
