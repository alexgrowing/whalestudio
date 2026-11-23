import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalChainsGlueCharPFibre
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
theorem _root_.GlobalTheory.T.local_chains_glue_char_p_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (E : ℕ → B.X.Modules) (ι : ∀ n, E n ⟶ freeModule B.X (Fin h)) (I : Type) (V : I → B.X.Opens) (D : ∀ i, ChainOn p h o Lie Om π γ (V i)) (hp : (p : Γ((fibI p B).subscheme, ⊤)) = 0), IsLoc M ι V D → ∀ n < o, ∀ (Q Q' : AM B Λ) (t : E n ⟶ Q.V) (t' : E (n + 1) ⟶ Q'.V), IsQuot M (ι n) (baseOn h π) Q t → IsQuot M (ι (n + 1)) (baseOn h π) Q' t' → Nonempty (Q ≅ frobA p hp Q') := by
  first | exact @GlobalTheory.ChainDesc.SheafPsi.main | exact GlobalTheory.ChainDesc.SheafPsi.main | (intros; apply GlobalTheory.ChainDesc.SheafPsi.main <;> assumption)
