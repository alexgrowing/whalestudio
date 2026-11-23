import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartGeneratorPullbackGeneratesFibreStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangentStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCombAtIffCoordinateCombinationStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinatesStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_frPt_tie : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R, (∀ τ i, M.Eig f τ (fun j => u τ j i)) → (∀ τ cv, M.Eig f τ cv → ∃! a : Fin (Dw.mult τ) → R, (u τ).mulVec a = cv) → ∃ y : FrPt Xo c R, y.x = x ∧ M.Comparison₂ f u y := by
  intro hT E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ u hu huniq
  have hover : x ≫ Xo.s = sOf c R := by
    rw [← Λ.xF_fst, Category.assoc, pullback.condition, ← Category.assoc, Λ.xF_snd]
    unfold sOf spMap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hV := GlobalTheory.T.lieBasis_coordinates_bijective_tangent E H Dw l Xo c O β Y M R f x Λ
  choose w hw _ using fun τ (i : Fin (Dw.mult τ)) => hV.1 (fun j => u τ j i)
  obtain ⟨s, hs, hgen⟩ := GlobalTheory.T.exists_chart_generator_pullback_generates_fibre hT E H Dw l Xo c O β Y M R f x Λ
  refine ⟨⟨x, hover, w, fun τ i => hV.2.1 _ _ (hw τ i),
    fun τ i => (GlobalTheory.T.isEigenvector_iff_lieBasis_coordinates E H Dw l Xo c O β Y M R f x Λ τ _ _ (hw τ i)).2 (hu τ i), ?_, s, hgen⟩,
    rfl, Λ, fun τ i => hw τ i, hs⟩
  intro τ v hvt hve
  obtain ⟨cv, hcv, hcvu⟩ := hV.2.2 v hvt
  have hcomb : ∀ a, IsCombAt x (w τ) a v ↔ Λ.Vec ((u τ).mulVec a) v := by
    intro a
    have hsum : (∑ i, a i • fun j => u τ j i) = (u τ).mulVec a := by
      funext j
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [GlobalTheory.T.isCombAt_iff_coordinate_combination E H Dw l Xo c O β Y M R f x Λ _ (fun i j => u τ j i) (w τ) a v (hw τ), hsum]
  have hcve : M.Eig f τ cv := (GlobalTheory.T.isEigenvector_iff_lieBasis_coordinates E H Dw l Xo c O β Y M R f x Λ τ cv v hcv).1 hve
  obtain ⟨a, ha, hau⟩ := huniq τ cv hcve
  refine ⟨a, (hcomb a).2 (ha ▸ hcv), fun a' ha' => hau a' ?_⟩
  exact hcvu _ ((hcomb a').1 ha')

end GlobalTheory.Reg
