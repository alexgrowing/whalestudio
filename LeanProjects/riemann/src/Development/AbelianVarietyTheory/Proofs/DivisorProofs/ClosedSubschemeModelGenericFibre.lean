import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSecOfNot

set_option autoImplicit false

noncomputable section

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

theorem isClosedEmbedding_up : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) [IsClosedImmersion j] (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ), IsClosedEmbedding (up j hj σ) := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z Y q j _ hj σ
  have hj' := isClosedEmbedding_comp (C := ℂ) j
  have hc : Continuous fun z : CxPts (genStr Z) σ => z.1 ≫ genι Z :=
    (continuous_comp (genι Z)).comp continuous_subtype_val
  refine ⟨IsEmbedding.of_comp (continuous_up j hj σ) hc ?_, ?_⟩
  · have h := hj'.isEmbedding.comp (IsEmbedding.subtypeVal (p := fun x : Sp ℂ ⟶ Y => x ≫ q = spMap (σ.comp β)))
    convert h using 1
    funext y
    exact up_ι j hj σ y
  · convert hj'.isClosed_range.preimage hc using 1
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, (up_ι j hj σ y).symm⟩
    · rintro ⟨x, hx⟩
      have hx' : x ≫ j = z.1 ≫ Limits.pullback.fst Z.s (spMap β) := hx
      have hz : z.1 ≫ Limits.pullback.snd Z.s (spMap β) = spMap σ := z.2
      refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩
      · show x ≫ q = spMap (σ.comp β)
        rw [← hj, ← Category.assoc, hx', Category.assoc, Limits.pullback.condition, ← Category.assoc, hz, ← Spec.map_comp]
        rfl
      · refine Limits.pullback.hom_ext ?_ ?_
        · exact (Limits.pullback.lift_fst _ _ _).trans hx'
        · exact (Limits.pullback.lift_snd _ _ _).trans hz.symm

end GlobalTheory.ArchLim

end
