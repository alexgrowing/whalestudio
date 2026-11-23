import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMarkedFormPiecesRaysOfSimplicialCells
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullAddInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearPullbackOfMarkedOrbitIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysAfterDroppingZeroCoordsStatement
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsDescendingRaysPullbackStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PullbackMemCellConeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsPullbackCoordinateOfPosStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.MatchingPieces

theorem exists_pieces_match : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim bar (⟨δ₀ i, h₀.mem i⟩ : balForms bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
  ∃ p : Fin m₀ → LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (p i) ∧
    (∀ i, 0 < t i → p i ∈ balForms bar X ∧ (∀ y, 0 ≤ p i y y) ∧
      (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = p i → k = 1) ∧
      ∀ lab : InvFun O, IsTwG w0 lab → lab.evalZ (p i) = lab.evalZ (δ₀ i)) ∧
    ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ → LinearIndependent ℤ δ →
      ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
        (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
        (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  intro O _ _ _ _ bar w0 hb φ hφ X₀ _ _ _ m₀ δ₀ h₀ hind hprim v t hv ht hvt X _ _ _ β hβ
  obtain ⟨τ, f, hτ, hf, hsemi, hrel⟩ := GlobalTheory.T.exists_semilinear_pullback_of_markedOrbitIndicator w0 v β hβ
  obtain ⟨u, hsum, hli, hu⟩ := GlobalTheory.T.exists_descending_rays_pullback O bar w0 hb δ₀ h₀.mem h₀.nonneg hind hprim v t ht hvt β τ f hτ hf hsemi hrel
  refine ⟨fun i => pullAdd f (u i), hsum, fun i hi => (hu i hi).2, ?_⟩
  intro m δ hδ hδi c hc hβc
  have hA := GlobalTheory.T.pullback_mem_cell_cone O bar w0 hb φ hφ δ₀ h₀ t ht (CarDim.orad v : Submodule O X₀).mkQ (Submodule.mkQ_surjective _) τ f hτ
    hf hsemi u (fun i hi => ⟨(hu i hi).1, (hu i hi).2.1, (hu i hi).2.2.1⟩) β hsum m δ hδ c hc hβc
  have hB := GlobalTheory.T.exists_pullback_coordinate_of_pos O bar w0 hb φ hφ δ₀ h₀ hind v t ht hvt (CarDim.orad v : Submodule O X₀).mkQ
    (Submodule.mkQ_surjective _) τ f hτ hf hsemi u (fun i hi => (hu i hi).1) β
    (fun x y x₀ y₀ hx hy => hrel x y x₀ y₀ hx hy) m δ hδ c hc hβc
  exact GlobalTheory.T.cone_match_rays_after_dropping_zero_coords (fun i => pullAdd f (u i)) t ht hli β hsum m δ hδi c hc hβc hA hB

end GlobalTheory.CompanionTheory.Ar.Fan.MatchingPieces
