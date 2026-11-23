import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChainCoverFreeModule
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
theorem _root_.GlobalTheory.T.pullback_chain_cover_free_module : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (B B' : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) (E : ℕ → B'.X.Modules) (ι : ∀ n, E n ⟶ freeModule B'.X (Fin h)) (Q : B'.X.Modules) (t : E 0 ⟶ Q) (j : ((pullA f.f).obj Lie).V ⟶ Q), Lie.V.IsQuasicoherent → IsSys C M → IsCov f g → IsLatOf C f g ι → ∀ (U : AffOp B.X) (S : Set (Γ(Om.V, U.1) × (C U).L 0)) (D : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U.1)), IsDown C f g U S D → JOn (ι 0) D t j → ∀ U' : AffOp B.X, U'.1 ≤ U.1 → JUp C f g U' (ι 0) t j := by
  first | exact @GlobalTheory.ChainDesc.UpSmallJ.main | exact GlobalTheory.ChainDesc.UpSmallJ.main | (intros; apply GlobalTheory.ChainDesc.UpSmallJ.main <;> assumption)
