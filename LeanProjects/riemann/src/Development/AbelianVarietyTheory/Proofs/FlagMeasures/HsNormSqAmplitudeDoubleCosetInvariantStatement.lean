import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqAmplitudeDoubleCosetInvariant
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hsNormSq_amplitude_doubleCoset_invariant : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (A : LocS W), GoodW D τ w w' θ W → 0 < Tr D w → 0 < Tr D w' → IsSPsiEquiv W.z (psiS D W.z) W.π A.Φ → IsSPsiEquiv W.z' (psiS D W.z') W.π' A.Φ' → ContinuousOn A.Φ (UH (Hpk D.R.k D.R.rS)) → ContinuousOn A.Φ' (UH (Hpk D.R.k D.R.rS)) → ∀ (γ a a' : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)) (ν ν' : Measure (Mt D.R.k D.R.rS)), RelPt D W.z W.z' γ p → a ∈ Sset D.R.k D.R.rS W.z → a' ∈ Sset D.R.k D.R.rS W.z' → RMeas D W γ 1 ν → RMeas D W (a * γ * a'⁻¹) 1 ν' → hsNormSq (A.J ν' (a * γ * a'⁻¹)) = hsNormSq (A.J ν γ) := by
  first | exact @GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset | exact GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset | (intros; apply GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset <;> assumption)
