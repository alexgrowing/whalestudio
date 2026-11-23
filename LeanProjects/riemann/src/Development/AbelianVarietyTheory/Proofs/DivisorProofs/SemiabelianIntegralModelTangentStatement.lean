import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianIntegralModelTangent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_integral_model_tangent : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (K : Type) [Field K] [NumberField K] (xO : Sp (𝓞 K) ⟶ X) (xK : Sp K ⟶ X) (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) (φ : Fib K) (m : CubeMap φ.G t.G), FibAt t xK φ m → ∀ (G : Over (Sp (𝓞 K))) [GrpObj G] (hG : IsSemiAbelian G) (θ : φ.P.A.left ⟶ G.left) (hθ : IsGrpPullback φ.P.A G (spMap (algebraMap (𝓞 K) K)) θ) (v : Fin φ.P.g → (epsR K ⟶ φ.P.A)) (hv : IsLieBasis v) (q : TanM xK t.G →ₗ[K] (Fin φ.P.g → K)), IsAbMap φ m v q → ∀ w : TanM xO t.G, q (bcTan (algebraMap (𝓞 K) K) hx w) ∈ (SemiFib.mk φ.P G hG θ hθ v hv).lieLat := by
  first | exact @GlobalTheory.BdFib.abMap_bcTan_mem_lieLat | exact GlobalTheory.BdFib.abMap_bcTan_mem_lieLat | (intros; apply GlobalTheory.BdFib.abMap_bcTan_mem_lieLat <;> assumption)
