import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMatrixActionCoordinates
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
theorem _root_.GlobalTheory.T.quotient_matrix_action_coordinates : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h : ℕ) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (H H' : AM B Λ) [H.V.IsQuasicoherent] [H'.V.IsQuasicoherent] (ι : H.V ⟶ freeModule B.X (Fin h)) [Mono ι] (ψ : H' ⟶ H), (∀ (a : Λ) (W : B.X.Opens) (s : Γ(H.V, W)), crd ι W ((H.ρ a : H.V ⟶ H.V).app W s) = mv (RingHom.id _) (M a) (crd ι W s)) → IsQuot M ι (fun W => latOf (ψ.hom ≫ ι) W) (cokernel ψ) (cokernel.π ψ).hom := by
  first | exact @GlobalTheory.ChainDesc.isQuot_cokernel | exact GlobalTheory.ChainDesc.isQuot_cokernel | (intros; apply GlobalTheory.ChainDesc.isQuot_cokernel <;> assumption)
