import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedLinearPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_linear_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) (D : Adapted A σ k) (hk : k < Dw.mult σ) (X' : Scheme.{0}) (f : X' ⟶ X) (L : D.C.Line f) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas M (f ≫ π) ty'), StepRel D hk L A' → IntStep A' σ (k + 1) := by
  first | exact @GlobalTheory.DRFlag.StepInt.intStep_succ | exact GlobalTheory.DRFlag.StepInt.intStep_succ | (intros; apply GlobalTheory.DRFlag.StepInt.intStep_succ <;> assumption)
