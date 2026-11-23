import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointFactorsAffineCover
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
theorem _root_.GlobalTheory.T.integral_point_factors_affine_cover : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) (k : IsCov f g) (K : Type) [Field K] [IsAlgClosed K] (R : Subring K), (∀ x : K, IsIntegral R x → x ∈ R) → ∀ (w : Sp R ⟶ B'.X) (U : AffOp B.X), ⊤ ≤ w ⁻¹ᵁ f.f ⁻¹ᵁ U.1 → ∃ φ : U.Bp →+* R, spMap φ ≫ U.toX = w ≫ f.f ∧ w = spMap (φ.comp (g U)) ≫ (k.isAffineOpen U).fromSpec := by
  first | exact @GlobalTheory.ChainDesc.IsCov.exists_extend | exact GlobalTheory.ChainDesc.IsCov.exists_extend | (intros; apply GlobalTheory.ChainDesc.IsCov.exists_extend <;> assumption)
