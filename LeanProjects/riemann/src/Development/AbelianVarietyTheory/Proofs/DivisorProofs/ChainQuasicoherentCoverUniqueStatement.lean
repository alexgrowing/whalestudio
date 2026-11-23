import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainQuasicoherentCoverUnique
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
theorem _root_.GlobalTheory.T.chain_quasicoherent_cover_unique : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (B B' : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp), Lie.V.IsQuasicoherent → Om.V.IsQuasicoherent → IsSys C M → IsCov f g → ∀ (U : AffOp B.X) (S : Set (Γ(Om.V, U.1) × (C U).L 0)) (D : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U.1)) (a : Λ), IsDown C f g U S D → Submodule.span Γ(B.X, U.1) {w | ∃ s ∈ S, s.1 = w ∧ ∃ s' ∈ S, s'.1 = (Om.ρ a : Om.V ⟶ Om.V).app _ w ∧ s'.2.1 = mv (RingHom.id _) (M a) s.2.1} = ⊤ → D.Map D (RingHom.id _) (M a) ((((pullA f.f).obj Lie).ρ a : ((pullA f.f).obj Lie).V ⟶ ((pullA f.f).obj Lie).V).app _) ((((pullA f.f).obj Om).ρ a : ((pullA f.f).obj Om).V ⟶ ((pullA f.f).obj Om).V).app _) := by
  first | exact @GlobalTheory.ChainDesc.DownAct.map_act | exact GlobalTheory.ChainDesc.DownAct.map_act | (intros; apply GlobalTheory.ChainDesc.DownAct.map_act <;> assumption)
