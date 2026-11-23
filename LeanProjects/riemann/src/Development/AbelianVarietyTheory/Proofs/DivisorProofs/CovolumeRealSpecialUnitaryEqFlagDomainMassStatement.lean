import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeRealSpecialUnitaryEqFlagDomainMass
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_realSpecialUnitary_eq_flagDomain_mass : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X))) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)], 1 ≤ r → (∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1) → IsOrth X x → IsFundSet X x FF → ENNReal.ofReal (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) * muF X x FF = covolume (inReal X.Ψ X.Gm X.Γ) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x) := by
  first | exact @GlobalTheory.SUCovol.covolume_realSU | exact GlobalTheory.SUCovol.covolume_realSU | (intros; apply GlobalTheory.SUCovol.covolume_realSU <;> assumption)
