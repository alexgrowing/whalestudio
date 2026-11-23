import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorThroughMonoLocalLifts
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
theorem _root_.GlobalTheory.T.factor_through_mono_local_lifts : ∀ (X : Scheme.{0}) (F E G : X.Modules) [F.IsQuasicoherent] [E.IsQuasicoherent] [G.IsQuasicoherent] (u : F ⟶ G) (ι : E ⟶ G) [Mono ι] (I : Type) (V : I → X.Opens), (∀ i, IsAffineOpen (V i)) → (∀ x : X, ∃ i, x ∈ V i) → (∀ i (s : Γ(F, V i)), ∃ s' : Γ(E, V i), ι.app _ s' = u.app _ s) → ∃ v : F ⟶ E, v ≫ ι = u := by
  first | exact @GlobalTheory.CoverHom.exists_factor_of_affineCover | exact GlobalTheory.CoverHom.exists_factor_of_affineCover | (intros; apply GlobalTheory.CoverHom.exists_factor_of_affineCover <;> assumption)
