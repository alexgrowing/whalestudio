import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAtlasRefiningCocycle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_atlas_refining_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (C : Coc X), ∃ A' : Atlas M π ty, (∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw M.t K), A'.FlagAt w u ↔ A.FlagAt w u) ∧ ∃ α : A'.ch.ι → C.A, ∀ a, ⊤ ≤ A'.ch.χ a ⁻¹ᵁ C.B (α a) := by
  first | exact @GlobalTheory.DRFlag.Atlas.exists_refine | exact GlobalTheory.DRFlag.Atlas.exists_refine | (intros; apply GlobalTheory.DRFlag.Atlas.exists_refine <;> assumption)
