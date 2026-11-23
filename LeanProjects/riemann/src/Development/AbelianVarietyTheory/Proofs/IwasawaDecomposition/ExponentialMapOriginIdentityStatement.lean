import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialMapOriginIdentity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_map_origin_identity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (σ : c.F →+* ℂ) (g : ℕ) (y : CxPts (genStr Z) σ) (ε : (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left)), ε 0 = (1 : Over.mk (y.1 ≫ genι Z) ⟶ Z.t.G).left → (∀ v, IsTanAtG Z.t (y.1 ≫ genι Z) v → ∃! w, IsDerivAt0 ε w v) → ∀ (f F : EigFrame Z σ (y.1 ≫ genι Z)) (W Wf : Letter Dw → Fin g → ℂ), (∀ z : Letter Dw, IsDerivAt0 ε (W z) (f.v z.1 z.2)) → (∀ z : Letter Dw, IsDerivAt0 ε (Wf z) (F.v z.1 z.2)) → ∀ (τ : E →+* ℂ) (v : Fin (Dw.mult τ) → ℂ), ∃ u : Fin (Dw.mult τ) → ℂ, ∑ b, v b • W ⟨τ, b⟩ = ∑ a, u a • Wf ⟨τ, a⟩ ∧ star v ⬝ᵥ x.gram y f τ *ᵥ v = star u ⬝ᵥ x.gram y F τ *ᵥ u := by
  first | exact @GlobalTheory.ShFam.Hor.ExpDirs.frameChange_dirs_gram | exact GlobalTheory.ShFam.Hor.ExpDirs.frameChange_dirs_gram | (intros; apply GlobalTheory.ShFam.Hor.ExpDirs.frameChange_dirs_gram <;> assumption)
