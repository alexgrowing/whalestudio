import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfFullIntStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDR_of_full_intStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀), (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) → (∀ σ, IntStep (atlasOf Z) σ (Dw.mult σ)) → HasDR Z := by
  first | exact @GlobalTheory.DRFlag.hasDR_of_intStep | exact GlobalTheory.DRFlag.hasDR_of_intStep | (intros; apply GlobalTheory.DRFlag.hasDR_of_intStep <;> assumption)
