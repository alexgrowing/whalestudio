import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.ExpDirs

theorem frameChange_dirs_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (σ : c.F →+* ℂ) (g : ℕ) (y : CxPts (genStr Z) σ) (ε : (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left)), ε 0 = (1 : Over.mk (y.1 ≫ genι Z) ⟶ Z.t.G).left → (∀ v, IsTanAtG Z.t (y.1 ≫ genι Z) v → ∃! w, IsDerivAt0 ε w v) → ∀ (f F : EigFrame Z σ (y.1 ≫ genι Z)) (W Wf : Letter Dw → Fin g → ℂ), (∀ z : Letter Dw, IsDerivAt0 ε (W z) (f.v z.1 z.2)) → (∀ z : Letter Dw, IsDerivAt0 ε (Wf z) (F.v z.1 z.2)) → ∀ (τ : E →+* ℂ) (v : Fin (Dw.mult τ) → ℂ), ∃ u : Fin (Dw.mult τ) → ℂ, ∑ b, v b • W ⟨τ, b⟩ = ∑ a, u a • Wf ⟨τ, a⟩ ∧ star v ⬝ᵥ x.gram y f τ *ᵥ v = star u ⬝ᵥ x.gram y F τ *ᵥ u := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ x σ g y ε e0 huniq f F W Wf hW hWf τ v
  set T := F.co f τ with hT
  have hg : x.gram y f τ = Tᴴ * x.gram y F τ * T := x.gram_change F f τ T (F.co_spec f τ)
  have hdir : ∀ i, W ⟨τ, i⟩ = ∑ a, T a i • Wf ⟨τ, a⟩ := fun i =>
    (huniq _ (f.tan τ i)).unique (hW ⟨τ, i⟩)
      (isDerivAt0_of_comb e0 (F.tan τ) (fun a => hWf ⟨τ, a⟩) (f.tan τ i) (F.co_spec f τ i))
  refine ⟨T *ᵥ v, ?_, ?_⟩
  · simp only [hdir, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]
  · rw [hg, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]

end GlobalTheory.ShFam.Hor.ExpDirs
