import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMapHoldsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationRayEventuallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationOnCoverGluesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationCoverTwistedInvariantStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem isTwInv_comb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {ψ φ : InvFun (𝓞 E)}
    (hψ : IsTwInv H ψ) (hφ : IsTwInv H φ) (x y : ℕ) : IsTwInv H (comb x ψ y φ) := by
  intro σ hσ n B
  show (x : ℝ) * ψ.toFun n _ + y * φ.toFun n _ = x * ψ.toFun n B + y * φ.toFun n B
  rw [hψ σ hσ, hφ σ hσ]

theorem polGlueSt : PolGlueSt := by
  intro E _ _ _ H D l Xo c I _ R _ a b ω C ψ φ k Cn hψ hφ hcov hC
  obtain ⟨bb, N, T₀, hb, hN, hp⟩ := GlobalTheory.T.polarization_ray_eventually C ψ φ k (fun i => (hC i).2)
  choose BD hBD using hp T₀ le_rfl
  have htw := fun T => isTwInv_comb hψ hφ (N * T) bb
  obtain ⟨Z, u, hu⟩ := GlobalTheory.T.polarization_cover_twisted_invariant GlobalTheory.T.polynomial_map_holds C _ _ BD (htw T₀) hcov hBD
  refine ⟨Z, GlobalTheory.T.cone_conditions_cover_models Cn Z C u hcov hu (fun i => (hC i).1), bb, N, T₀, hb, hN, fun T hT => ?_⟩
  choose BD' hBD' using hp T hT
  exact GlobalTheory.T.polarization_on_cover_glues GlobalTheory.T.polynomial_map_holds Z C u _ _ BD' (htw T) hcov hu hBD'

end GlobalTheory.TorRef
