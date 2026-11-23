import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRamificationCompleteDVRValuationEqMul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ramification_completeDVR_valuation_eq_mul : ∀ (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∃ e : ℕ, 0 < e ∧ ∀ z : K, vV T.V (iK z) = (e : ℤ) * vAdd 𝔓 z := by
  first | exact @GlobalTheory.CdvrPlaceVal.vV_eq_mul_vAdd | exact GlobalTheory.CdvrPlaceVal.vV_eq_mul_vAdd | (intros; apply GlobalTheory.CdvrPlaceVal.vV_eq_mul_vAdd <;> assumption)
