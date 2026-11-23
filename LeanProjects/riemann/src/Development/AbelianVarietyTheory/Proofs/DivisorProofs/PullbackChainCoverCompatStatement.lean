import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChainCoverCompat
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
theorem _root_.GlobalTheory.T.pullback_chain_cover_compat : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (B B' : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) (E : ℕ → B'.X.Modules) (ι : ∀ n, E n ⟶ freeModule B'.X (Fin h)) (Q : AM B' Λ) (t : E 0 ⟶ Q.V) (j : (pullA f.f).obj Lie ⟶ Q) (ρ : (pullA f.f).obj Om ⟶ cokernel j) (k : IsCov f g), Lie.V.IsQuasicoherent → IsLatOf C f g ι → IsQuot M (ι 0) (baseOn h (f.f.appTop π)) Q t → ∀ U : AffOp B.X, JUp C f g U (ι 0) t j.hom → RUp C f g U (ι 0) (t ≫ (cokernel.π j).hom) ρ.hom → ∀ (R : Type) [CommRing R] (φ : U.Bp →+* R), φ (cstBp U π) ∈ nonZeroDivisors R → ∀ (hw : ⊤ ≤ (spMap (φ.comp (g U)) ≫ (k.isAffineOpen U).fromSpec) ⁻¹ᵁ f.f ⁻¹ᵁ U.1) (r : ℕ) (e : Fin r → Γ(Om.V, U.1)), kerAt (spMap (φ.comp (g U)) ≫ (k.isAffineOpen U).fromSpec) ρ.hom hw (fun l => pullbackSections f.f Om.V le_rfl (e l)) = (C U).kerR φ fun l => 1 ⊗ₜ e l := by
  first | exact @GlobalTheory.ChainDesc.KerRho.kerAt_eq_kerR | exact GlobalTheory.ChainDesc.KerRho.kerAt_eq_kerR | (intros; apply GlobalTheory.ChainDesc.KerRho.kerAt_eq_kerR <;> assumption)
