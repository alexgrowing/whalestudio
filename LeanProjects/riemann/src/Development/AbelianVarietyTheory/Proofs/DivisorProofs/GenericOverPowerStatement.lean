import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericOverPower
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_over_power : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (f : Y.X → Y.Fn) (ψ φ : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (l m : ℕ) (a : ℤ), l ≠ 0 → 0 < m → (∀ v e y, (l : 𝓞 F) ∈ v.asIdeal → φ v e y = m * ψ v e y + a * Real.log (e.w (l : AlgebraicClosure F))) → GenOver V f ψ l → GenOver V (fun y => f y ^ m) φ l := by
  first | exact @GlobalTheory.HtGen.genOver_pow_div | exact GlobalTheory.HtGen.genOver_pow_div | (intros; apply GlobalTheory.HtGen.genOver_pow_div <;> assumption)
