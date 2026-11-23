import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstantIffCoveringGroupInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreConstant_iff_coveringGroup_invariant : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → ((Dw.p ≠ Dw.q ∧ l.A = 1) ∨ GlobalTheory.ClsVal.Cmp.OverBase d) → ∀ (lift : Gam Dw d.l₂ → Dw.La →ₗ[𝓞 D.host.E] Dw.La), IsLift lift → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec d.Xo₂ d.c₂ a n, (FibConst d g ↔ ∀ γ, CongMod l.Mb (lift γ) LinearMap.id → actLev d.c₂ (fun γ => (lift γ, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) γ g = g) := by
  first | exact @GlobalTheory.LevInv.fibConst_iff_invariant | exact GlobalTheory.LevInv.fibConst_iff_invariant | (intros; apply GlobalTheory.LevInv.fibConst_iff_invariant <;> assumption)
