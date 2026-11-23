import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasModelComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_model_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (Z : Mdl Y i₀), p.Prime → (p : ℂ) ∈ W.nonunits → Geo (Y i) π → i.c.F ≤ Z.i.c.F → (∀ σ, ty σ ⊆ Z.ty σ) → LocMaps Z A → ∃ h, MapsTo Z A h := by
  first | exact @GlobalTheory.DRFlag.exists_mapsTo | exact GlobalTheory.DRFlag.exists_mapsTo | (intros; apply GlobalTheory.DRFlag.exists_mapsTo <;> assumption)
