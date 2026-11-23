import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedClosureLocalSystem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_closure_local_system : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hk : k < Dw.mult σ) (Sb : D.C.Sub A.ch r) (Cl : Sb.Closure (π ≫ (Y i).s)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y i) (Cl.f ≫ π) ty') (Z : Mdl Y i₀) (g : Z.X ⟶ X), StepRel D hk Cl.L A' → HasDR Z → MapsTo Z A g → LocMaps Z A' := by
  first | exact @GlobalTheory.DRFlag.locMaps_closure_of_hasDR | exact GlobalTheory.DRFlag.locMaps_closure_of_hasDR | (intros; apply GlobalTheory.DRFlag.locMaps_closure_of_hasDR <;> assumption)
