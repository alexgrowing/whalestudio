import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartDirectionalDerivativeRegularCoordinate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmoothOnPreimageChartsStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam

namespace GlobalTheory.KaehlerFamily

variable {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {d : ℕ} {σ σ' : k →+* ℂ}

theorem mem_ptsIn_conj {j : CxPts p σ' → CxPts p σ} (hj : IsConjMap j) {U : Y.Opens} {z : CxPts p σ'}
    (hz : z ∈ ptsIn p σ' U) : j z ∈ ptsIn p σ U := by
  rw [mem_ptsIn] at hz ⊢
  rw [hj z]
  have e : ∀ a b : PrimeSpectrum ℂ, a = b := fun a b => Subsingleton.elim a b
  exact (congrArg (· ∈ U) ((Scheme.Hom.comp_apply _ _ _).trans (congrArg z.1 (e _ _)))).mpr hz

theorem isPotential_conj [SmoothOfRelativeDimension d p] {B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y} {ψ : Weight p σ B}
    {ψ' : Weight p σ' B} (h : ψ.IsSmooth (AnRead.all p σ d)) (hc : ψ'.IsConj ψ)
    {j : CxPts p σ' → CxPts p σ} (hj : IsConjMap j) {W : Set (CxPts p σ)} {φ : CxPts p σ → ℝ}
    (hφ : IsPotential (AnRead.all p σ d) (curvForm ψ) W φ) :
    IsPotential (AnRead.all p σ' d) (curvForm ψ') (j ⁻¹' W) (φ ∘ j) := by
  obtain ⟨ho, hs, H⟩ := GlobalTheory.T.conj_smoothOn_preimage_charts k Y p d σ σ' j hj W φ hφ.1 hφ.2.1
  refine ⟨ho, hs, fun c' z hz hW ξ => ?_⟩
  obtain ⟨c, hc', e⟩ := H c' z hz
  have hi := mem_pick ψ'.isLB z
  rw [e, ← hφ.2.2 c _ hc' hW, (isPotential_curvForm h (pick ψ'.isLB z)).2.2 c _ hc' (mem_ptsIn_conj hj hi), ← e]
  exact congrArg (· / Real.pi) (AlgChart.levi_congr (isOpen_ptsIn _) hz hi
    (fun y hy => (hc _ y (j y) (hj y) hy).symm) ξ)

theorem exists_kaehlerFamily : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ)
    [SmoothOfRelativeDimension d p], IsProjOver p → ∃ a : ∀ σ : k →+* ℂ, ChartForm p σ d,
      (∀ σ, IsKaehlerForm (AnRead.all p σ d) (a σ)) ∧ ∀ σ σ' (j : CxPts p σ' → CxPts p σ), IsConjMap j →
        ∀ W φ, IsPotential (AnRead.all p σ d) (a σ) W φ →
          IsPotential (AnRead.all p σ' d) (a σ') (j ⁻¹' W) (φ ∘ j) := by
  rintro k _ Y p d _ ⟨N, i, _, h⟩
  refine ⟨fun σ => curvForm ((ProjAn.fsO1 k σ N).pull i h), fun σ =>
    isKaehlerForm_curvForm (ProjPos.fubiniStudy_weight_pullback_isSmooth i h _) (ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos i h _),
    fun σ σ' j hj W φ hφ => isPotential_conj (ProjPos.fubiniStudy_weight_pullback_isSmooth i h _) ?_ hj hφ⟩
  exact (Weight.isConj_fsBasis _ _ _ _ _ (Matrix.map_one _ (map_zero _) (map_one _)).symm).pull i h

end GlobalTheory.KaehlerFamily
