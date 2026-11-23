import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.OddPrimesWithRootsOfUnity

theorem gram_continuousOn_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (σ : c.F →+* ℂ) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (T : Type) [TopologicalSpace T] (a : T → CxFr Z σ) (S : Set T), ContinuousOn (fun t => (a t).1) S → (∀ t ∈ S, ∃ hy : (a t).1 ∈ ptsIn (genStr Z) σ V.1, F.IsMap (evHom hy) (a t).2) → ∀ τ : E →+* ℂ, ContinuousOn (fun t => x.gram (a t).1 (a t).2 τ) S := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ x σ V φ F T _ a S ha hF τ
  refine continuousOn_pi.2 fun a' => continuousOn_pi.2 fun b' => ?_
  obtain ⟨g, h1, h2, h3⟩ := x.gram_smooth (σ := σ) V F τ a' b'
  have hre := h1.continuousOn (isOpen_ptsIn _)
  have him := h2.continuousOn (isOpen_ptsIn _)
  have hg : ContinuousOn g (ptsIn (genStr Z) σ V.1) := by
    have hc : ContinuousOn (fun y => ((g y).re : ℂ) + ((g y).im : ℂ) * Complex.I) (ptsIn (genStr Z) σ V.1) :=
      (Complex.continuous_ofReal.comp_continuousOn hre).add
        ((Complex.continuous_ofReal.comp_continuousOn him).mul continuousOn_const)
    exact hc.congr fun y _ => (Complex.re_add_im (g y)).symm
  have hmaps : Set.MapsTo (fun t => (a t).1) S (ptsIn (genStr Z) σ V.1) := fun t ht => (hF t ht).1
  refine (hg.comp ha hmaps).congr fun t ht => ?_
  obtain ⟨hy, hm⟩ := hF t ht
  exact h3 _ hy _ (hm τ)

end GlobalTheory.ShFam.OddPrimesWithRootsOfUnity
