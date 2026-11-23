import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasPullbackPreservesStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_pullback_preserves_step : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) (X' : Scheme.{0}) (f : X' ⟶ X) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas M (f ≫ π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : Vecs Dw M.t K), A'.FlagAt w u → A.FlagAt (w ≫ f) u) → IntStep A σ k → IntStep A' σ k := by
  first | exact @GlobalTheory.DRFlag.IntStep.pull | exact GlobalTheory.DRFlag.IntStep.pull | (intros; apply GlobalTheory.DRFlag.IntStep.pull <;> assumption)
