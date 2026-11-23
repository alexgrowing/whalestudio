import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianLieBasisComparison
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_lie_basis_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (K : Type) [Field K] [NumberField K] (xK : Sp K ⟶ X) (φ : Fib K) (m : CubeMap φ.G t.G), FibAt t xK φ m → ∀ (G : Over (Sp (𝓞 K))) [GrpObj G] (hG : IsSemiAbelian G) (θ : φ.P.A.left ⟶ G.left) (hθ : IsGrpPullback φ.P.A G (spMap (algebraMap (𝓞 K) K)) θ) (v : Fin φ.P.g → (epsR K ⟶ φ.P.A)) (hv : IsLieBasis v) (h' : HermFam K (Fin φ.P.g → K)), (SemiFib.mk φ.P G hG θ hθ v hv).IsHerm h' → ∀ q : TanM xK t.G →ₗ[K] (Fin φ.P.g → K), IsAbMap φ m v q → ∀ (σ : K →+* ℂ) (z : Sp ℂ ⟶ X) (hz : spMap σ ≫ xK = z) (g : TanM z t.G →ₗ[ℂ] TanM z t.G →ₗ⋆[ℂ] ℂ) (C : ℝ), IsBlockMetric g → AbLe g C → ∀ (n : ℕ) (w : Fin n → TanM xK t.G), ((C : ℂ) • gramOf g (fun i => bcTan σ hz (w i)) - h'.gram σ (fun i => q (w i))).PosSemidef := by
  first | exact @GlobalTheory.ArchAbBound.gram_le | exact GlobalTheory.ArchAbBound.gram_le | (intros; apply GlobalTheory.ArchAbBound.gram_le <;> assumption)
