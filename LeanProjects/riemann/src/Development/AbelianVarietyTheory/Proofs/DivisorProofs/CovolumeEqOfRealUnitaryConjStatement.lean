import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConj
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_eq_of_realUnitary_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x0 : Frame X.Ψ r) (x0' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) → (∀ γ ∈ X.Γ, ∃ γ' ∈ X'.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → (∀ γ' ∈ X'.Γ, ∃ γ ∈ X.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → IsOrth X x0 → IsOrth X' x0' → IsFundSet X x0 FF → IsFundSet X' x0' FF' → muF X x0 FF = muF X' x0' FF' := by
  first | exact @GlobalTheory.CovolConj.muF_eq_of_conj | exact GlobalTheory.CovolConj.muF_eq_of_conj | (intros; apply GlobalTheory.CovolConj.muF_eq_of_conj <;> assumption)
