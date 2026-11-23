import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsNormalModelVectorBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain)
open GlobalTheory.ChainPts.PullHT (pullA)
open scoped TensorProduct
open GlobalTheory.ChainPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chains_normal_model_vector_bundle : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] [Module.Finite ℤ Λ] (h o r r' : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ), GlobalTheory.IsNormalScheme B.X → IsAdd Lie → IsAdd Om → GlobalTheory.VB.IsVB Lie.V r → GlobalTheory.VB.IsVB Om.V r' → IsRootOfP p π (p - 1) → (∀ k ≤ o, IsRootOfP p (γ k) (p ^ (k + 1))) → IsSys C M → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (P : PreChain p o ((pullA f.f).obj Lie) ((pullA f.f).obj Om) (f.f.appTop π)), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ KerMatch C f.f P.j.hom P.ρ.hom := by
  first | exact @GlobalTheory.ChainDesc.exists_preChain_kerMatch | exact GlobalTheory.ChainDesc.exists_preChain_kerMatch | (intros; apply GlobalTheory.ChainDesc.exists_preChain_kerMatch <;> assumption)
