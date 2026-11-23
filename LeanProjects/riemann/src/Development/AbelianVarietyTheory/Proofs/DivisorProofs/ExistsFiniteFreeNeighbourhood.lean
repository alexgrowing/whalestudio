import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsZpowMulIsUnitOfMem
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
open GlobalTheory.IrrAn

noncomputable section

namespace GlobalTheory.IrrAn

open CategoryTheory AlgebraicGeometry Limits

theorem ptsOf_nonempty (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [LocallyOfFiniteType p] (σ : k →+* ℂ) (T : Set (Limits.pullback p (spMap σ) : Scheme.{0}))
    (hT : IsLocallyClosed T) (hne : T.Nonempty) : (GlobalTheory.IrrAn.ptsOf p σ T).Nonempty := by
  obtain ⟨x, hx, hxT⟩ := GlobalTheory.ZH.FrameNorm.exists_point_mem (K := ℂ) (C := ℂ)
    (pullback.snd p (spMap σ)) (RingHom.id ℂ) hT hne
  have hx' : x ≫ pullback.snd p (spMap σ) = 𝟙 _ := hx.trans (Spec.map_id _)
  refine ⟨⟨x ≫ pullback.fst p (spMap σ), ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hx', Category.id_comp]
  · have he : pt p σ ⟨x ≫ pullback.fst p (spMap σ), by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hx', Category.id_comp]⟩ = x := by
      apply pullback.hom_ext
      · exact pullback.lift_fst _ _ _
      · exact (pullback.lift_snd _ _ _).trans hx'.symm
    show pt p σ _ (IsLocalRing.closedPoint ℂ) ∈ T
    rw [he]
    exact hxT _

end GlobalTheory.IrrAn

end
