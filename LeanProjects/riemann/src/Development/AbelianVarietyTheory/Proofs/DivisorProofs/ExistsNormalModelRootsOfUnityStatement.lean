import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelRootsOfUnity
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
theorem _root_.GlobalTheory.T.exists_normal_model_roots_of_unity : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ n : ℕ, ∃ (B' : GlobalTheory.Vert.Model O) (g : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ g.relDim = 0 ∧ ∃ ζ : Γ(B'.X, ⊤), IsPrimitiveRoot ζ (p ^ n) := by
  first | exact @GlobalTheory.ChainPts.exists_cover_primitiveRoot | exact GlobalTheory.ChainPts.exists_cover_primitiveRoot | (intros; apply GlobalTheory.ChainPts.exists_cover_primitiveRoot <;> assumption)
