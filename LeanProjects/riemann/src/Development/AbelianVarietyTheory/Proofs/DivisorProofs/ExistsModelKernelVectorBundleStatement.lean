import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelKernelVectorBundle
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
theorem _root_.GlobalTheory.T.exists_model_kernel_vector_bundle : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O) (r : ℕ) (F Q : B.X.Modules) (u : F ⟶ Q), GlobalTheory.IsNormalScheme B.X → GlobalTheory.VB.IsVB F r → Q.IsQuasicoherent → Epi u → IsZero (B.genRes.obj Q) → ∃ (B' : GlobalTheory.Vert.Model O) (g : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ g.relDim = 0 ∧ GlobalTheory.VB.IsVB (kernel ((Scheme.Modules.pullback g.f).map u)) r := by
  first | exact @GlobalTheory.KernelModif.main | exact GlobalTheory.KernelModif.main | (intros; apply GlobalTheory.KernelModif.main <;> assumption)
