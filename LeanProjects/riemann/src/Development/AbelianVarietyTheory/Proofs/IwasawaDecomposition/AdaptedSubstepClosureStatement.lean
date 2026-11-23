import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedSubstepClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_substep_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (Sb : D.C.Sub A.ch r) (Cl : Sb.Closure (π ≫ M.s)) (ty' : (E →+* ℂ) → Finset ℕ), IsFrSub D Sb hj → (k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) → (∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e) → ty' σ = insert (k + 1) (ty σ) → (∀ σ', σ' ≠ σ → ty' σ' = ty σ') → ∃ A' : Atlas M (Cl.f ≫ π) ty', StepRel D hk Cl.L A' := by
  first | exact @GlobalTheory.DRFlag.StepAtlas.exists_stepAtlas | exact GlobalTheory.DRFlag.StepAtlas.exists_stepAtlas | (intros; apply GlobalTheory.DRFlag.StepAtlas.exists_stepAtlas <;> assumption)
