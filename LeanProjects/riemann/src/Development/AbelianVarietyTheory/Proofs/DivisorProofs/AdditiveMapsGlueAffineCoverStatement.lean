import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveMapsGlueAffineCover
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
theorem _root_.GlobalTheory.T.additive_maps_glue_affine_cover : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (hp : (p : Γ((fibI p B).subscheme, ⊤)) = 0) (F G : AM B Λ) [F.V.IsQuasicoherent] [G.V.IsQuasicoherent] (I : Type) (V : I → B.X.Opens) (k : ℕ) (ψ : ∀ i, Γ(F.V, V i) →+ Γ(G.V, V i)), (∀ i, IsAffineOpen (V i)) → (∀ x : B.X, ∃ i, x ∈ V i) → (∀ i i', IsAffineOpen (V i ⊓ V i')) → (∀ i, IsFrobLin Γ(B.X, V i) p (p ^ (k + 1)) (ψ i)) → (∀ i i', ∃ χ : Γ(F.V, V i ⊓ V i') →+ Γ(G.V, V i ⊓ V i'), IsFrobLin Γ(B.X, V i ⊓ V i') p (p ^ (k + 1)) χ ∧ (∀ s, χ (resM F.V inf_le_left s) = resM G.V inf_le_left (ψ i s)) ∧ ∀ s, χ (resM F.V inf_le_right s) = resM G.V inf_le_right (ψ i' s)) → (∀ (i : I) (a : Λ) (s : Γ(F.V, V i)), ψ i ((F.ρ a : F.V ⟶ F.V).app _ s) = (G.ρ a : G.V ⟶ G.V).app _ (ψ i s)) → Nonempty ((frobA p hp)^[k + 1] F ≅ G) := by
  first | exact @GlobalTheory.ChainPts.FrobGlue.main | exact GlobalTheory.ChainPts.FrobGlue.main | (intros; apply GlobalTheory.ChainPts.FrobGlue.main <;> assumption)
