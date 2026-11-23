import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationPowerBounds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_power_bounds : ∀ {F : Type} [Field F] [NumberField F] (p n k : ℕ), p.Prime → n ≠ 0 → ∃ k' : ℕ,
    ∀ v : HeightOneSpectrum (𝓞 F), resP v = p → ∀ e : Ext v,
      e.w (p : AlgebraicClosure F) ^ k' / e.w (n : AlgebraicClosure F) ^ 3 ≤ e.w (p : AlgebraicClosure F) ^ k ∧
      e.w (p : AlgebraicClosure F) ^ k' / e.w (n : AlgebraicClosure F) ^ 2 < 1 ∧ e.w (p : AlgebraicClosure F) ^ k' < 1 := by
  first | exact @GlobalTheory.ConstLat.exists_prec_consts | exact GlobalTheory.ConstLat.exists_prec_consts | (intros; apply GlobalTheory.ConstLat.exists_prec_consts <;> assumption)
