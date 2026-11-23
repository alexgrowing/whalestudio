import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixActionGeneratedAdditive
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
theorem _root_.GlobalTheory.T.matrix_action_generated_additive : ∀ (p h o : ℕ) (A Λ : Type) [CommRing A] [CommRing Λ] (π : A) (γ : ℕ → A) (Lie Om : Type) [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] (D : RChain p A h o π γ Lie Om) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (α : Λ → Lie → Lie) (β : Λ → Om → Om) (G : Set Λ), (∀ a b y, α (a + b) y = α a y + α b y) → (∀ a b y, β (a + b) y = β a y + β b y) → Submodule.span ℤ G = ⊤ → (∀ a ∈ G, D.Map D (RingHom.id A) (M a) (α a) (β a)) → ∀ a, D.Map D (RingHom.id A) (M a) (α a) (β a) := by
  first | exact @GlobalTheory.ChainDesc.MapAdd.map_of_span | exact GlobalTheory.ChainDesc.MapAdd.map_of_span | (intros; apply GlobalTheory.ChainDesc.MapAdd.map_of_span <;> assumption)
