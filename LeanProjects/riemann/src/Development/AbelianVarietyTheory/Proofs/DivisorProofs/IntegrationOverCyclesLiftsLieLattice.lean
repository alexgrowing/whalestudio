import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallChartPairAlongLinearMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticChartsRealizationOfAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderJetAlgHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentOfUniformisationJetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalBoundOfPeriodClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOnTangentEqDerivativeBoundingFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivEqFderivZeroOfConstDifferences

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem pLie_holds : PLie := by
  intro A _ g hA _ L u P hP x
  have hs := GlobalTheory.T.abelianScheme_isSeparated_of_affine_base A hA
  obtain ⟨K, -, -, hK, hsm, -⟩ := GlobalTheory.T.exists_small_chart_pair_along_linear_map (fibUnif u) (fibUnif u) id analyticOnNhd_id (fun _ h ↦ h)
    LinearMap.id (AddMonoidHom.id _) (fun _ _ _ ↦ rfl)
  obtain ⟨r, hr, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine (fibUnif u) hs K hsm
  obtain ⟨k, hk⟩ := hK.1 0 trivial
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_firstOrderJet_algHom (K.W k) 0 hk (0, (x : Fin g → ℂ))
  obtain ⟨v, hv, ht, hd⟩ := GlobalTheory.T.exists_tangent_of_uniformisation_jet u hs (K.W k) (r.x k) (hr k)
    ((congrArg (r.x k ≫ ·) (Category.comp_id A.hom).symm).trans (r.w k)) hk x ρ hρ
  refine ⟨v, ⟨ht, fun f hf ↦ ?_⟩, hd⟩
  obtain ⟨q, G, hq, hG, hGk, hGl⟩ := GlobalTheory.T.exists_global_bound_of_period_class K hK r f _ (hP ⟨_, hf⟩ K r hr)
  rw [GlobalTheory.T.form_on_tangent_eq_derivative_bounding_function K r k 0 hk x ρ hρ v hv f _ q hq, Hol.fderiv_fn_congr _ (hGk k) hk]
  have hdG : ∀ p, DifferentiableAt ℂ G p := fun p ↦ (hG p trivial).differentiableAt
  have hi : ∀ w : Fin g → ℂ, HasFDerivAt (fun w : Fin g → ℂ ↦ ((0, w) : Tot Empty g))
      (ContinuousLinearMap.inr ℂ (Empty → ℂ) (Fin g → ℂ)) w := fun w ↦ hasFDerivAt_prodMk_right _ _
  have := GlobalTheory.fderiv_zero_eq_of_const_differences u.Λ u.full (fun w ↦ G (0, w)) (fun l ↦ P l ⟨_, hf⟩)
    (fun w ↦ (hdG _).comp w (hi w).differentiableAt)
    (fun l w ↦ (hGl l (0, w) trivial).trans (congrArg (G (0, w) + ·) (Hol.fn_algebraMap _ trivial))) x
  rw [← this]
  exact congrArg (fun D : (Fin g → ℂ) →L[ℂ] ℂ ↦ D x) ((hdG (0, 0)).hasFDerivAt.comp (0 : Fin g → ℂ) (hi 0)).fderiv

end GlobalTheory.AnPer
