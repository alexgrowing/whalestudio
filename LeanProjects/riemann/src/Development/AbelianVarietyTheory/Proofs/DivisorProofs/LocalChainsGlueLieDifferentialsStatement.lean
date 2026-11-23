import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalChainsGlueLieDifferentials
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
theorem _root_.GlobalTheory.T.local_chains_glue_lie_differentials : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (E : ℕ → B.X.Modules) (ι : ∀ n, E n ⟶ freeModule B.X (Fin h)) (I : Type) (V : I → B.X.Opens) (D : ∀ i, ChainOn p h o Lie Om π γ (V i)), Lie.V.IsQuasicoherent → Om.V.IsQuasicoherent → IsLoc M ι V D → ∀ (Q : AM B Λ) (t : E 0 ⟶ Q.V), IsQuot M (ι 0) (baseOn h π) Q t → ∀ j : Lie ⟶ Q, (∀ i, JOn (ι 0) (D i) t j.hom) → (∀ (i : I) (W : B.X.Opens) (hle : W ≤ V i) (D' : ChainOn p h o Lie Om π γ W), IsAffineOpen W → Fits ι D' → ResMap hle (D i) D' → JOn (ι 0) D' t j.hom) → ∃ ρ : Om ⟶ cokernel j, Epi ρ ∧ ∀ i, ROn (ι 0) (D i) (t ≫ (cokernel.π j).hom) ρ.hom := by
  first | exact @GlobalTheory.ChainDesc.SheafRho.main | exact GlobalTheory.ChainDesc.SheafRho.main | (intros; apply GlobalTheory.ChainDesc.SheafRho.main <;> assumption)
