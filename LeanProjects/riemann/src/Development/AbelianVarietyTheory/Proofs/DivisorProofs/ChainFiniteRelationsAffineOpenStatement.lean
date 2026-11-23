import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFiniteRelationsAffineOpen
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
theorem _root_.GlobalTheory.T.chain_finite_relations_affine_open : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o r r' : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (C : ChainsBp p h o Lie Om π γ), GlobalTheory.VB.IsVB Lie.V r → GlobalTheory.VB.IsVB Om.V r' → ∀ (U : AffOp B.X) (S : Set (Γ(Om.V, U.1) × (C U).L 0)), S.Finite → cstBp U π ≠ 0 → (∀ s ∈ S, (C U).ρ (1 ⊗ₜ s.1) = Submodule.Quotient.mk (Submodule.Quotient.mk s.2)) → ∃ T : Set U.Bp, T.Finite ∧ ∀ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp), IsCov f g → T ⊆ Set.range (g U) → ∃ D : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U.1), IsDown C f g U S D := by
  first | exact @GlobalTheory.ChainDesc.exists_isDown | exact GlobalTheory.ChainDesc.exists_isDown | (intros; apply GlobalTheory.ChainDesc.exists_isDown <;> assumption)
