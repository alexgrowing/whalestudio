import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCaseCuspFormFibreSlopeGeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveEigenlatticeSlopeDefiniteStatement
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt

theorem eigLat_slope_definite : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : Type) [Group G] [Finite G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (χ : G →* (c.F)ˣ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Finite (Comp Xo c) → Nonempty (Comp Xo c) → (∀ σ, GoodEmb c σ → ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom) → ActLev (Xo := Xo) c lev → FreePt Xo c lev → Dom a n → GoodW U ξ V dict (wtZ a n) → FlatExistsAt U ξ c₁ → eigLat U lev χ (wtZ a n) ≠ ⊥ ∧ defBound Dw a n c₁ ≤ slope_sq (normW U ξ V dict (wtZ a n)) (eigLat U lev χ (wtZ a n)) / 2 := by
  intro D H Dw l Xo c r U ξ V dict G _ _ lev χ a n c₁ hD hF hN hdom hA hfree hDom hW hflat
  exact GlobalTheory.T.levelMove_eigenlattice_slope_definite D H Dw l Xo c r U ξ V dict G lev χ a n (defBound Dw a n c₁) hD hF hN hdom hA hfree hDom hW
    (GlobalTheory.T.definiteCase_cuspForm_fibre_slope_ge_bound D.host.E H Dw l Xo c r U ξ a n c₁ hD hDom hflat)

end GlobalTheory.DefPt
