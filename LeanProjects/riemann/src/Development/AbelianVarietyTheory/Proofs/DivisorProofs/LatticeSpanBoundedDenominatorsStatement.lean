import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpanBoundedDenominators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_span_bounded_denominators : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp), IsCov f g → ∀ (h : ℕ) (E : B'.X.Modules) (ι : E ⟶ freeModule B'.X (Fin h)), GlobalTheory.VB.IsVB E h → Mono ι → ∀ (U : AffOp B.X) (L : Submodule U.Bp (Fin h → U.Bp)) (c : U.Bp), c ≠ 0 → (∀ x : Fin h → U.Bp, c • x ∈ L) → L = Submodule.span U.Bp (piMap (g U) (Fin h) '' (latOf ι (f.f ⁻¹ᵁ U.1) : Set _)) → latOf ι (f.f ⁻¹ᵁ U.1) = L.comap (piMap (g U) (Fin h)) := by
  first | exact @GlobalTheory.ChainDesc.latOf_eq_comap_of_span | exact GlobalTheory.ChainDesc.latOf_eq_comap_of_span | (intros; apply GlobalTheory.ChainDesc.latOf_eq_comap_of_span <;> assumption)
