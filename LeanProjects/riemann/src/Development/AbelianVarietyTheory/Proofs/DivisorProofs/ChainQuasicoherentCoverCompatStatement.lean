import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainQuasicoherentCoverCompat
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
theorem _root_.GlobalTheory.T.chain_quasicoherent_cover_compat : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (B B' : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp), Lie.V.IsQuasicoherent → Om.V.IsQuasicoherent → IsSys C M → IsCov f g → ∀ (U U' : AffOp B.X) (hle : U'.1 ≤ U.1) (S : Set (Γ(Om.V, U.1) × (C U).L 0)) (S' : Set (Γ(Om.V, U'.1) × (C U').L 0)) (D : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U.1)) (D' : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U'.1)), IsDown C f g U S D → IsDown C f g U' S' D' → Submodule.span Γ(B.X, U.1) {w | ∃ s ∈ S, s.1 = w ∧ ∃ s' ∈ S', s'.1 = resM Om.V hle w ∧ s'.2.1 = piMap (AffOp.res hle) (Fin h) s.2.1} = ⊤ → ResMap (f.f.preimage_mono hle) D D' := by
  first | exact @GlobalTheory.ChainDesc.DownRes.down_res | exact GlobalTheory.ChainDesc.DownRes.down_res | (intros; apply GlobalTheory.ChainDesc.DownRes.down_res <;> assumption)
