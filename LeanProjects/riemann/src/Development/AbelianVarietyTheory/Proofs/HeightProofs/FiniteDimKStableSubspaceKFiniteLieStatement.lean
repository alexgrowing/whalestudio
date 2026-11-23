import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDim_kStable_subspace_kFinite_lie : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → (∀ S : Submodule ℂ R.U.H, FiniteDimensional ℂ S → IsKStableOn ε σ S → S ≤ LinearMap.range R.ι) ∧ ∀ W : Submodule ℂ R.HK.V, FiniteDimensional ℂ W → IsKStableOn ε σ (W.map R.ι) → KStable R.HK.act W := by
  first | exact @GlobalTheory.RealPar.KStabLie.kstable_lie | exact GlobalTheory.RealPar.KStabLie.kstable_lie | (intros; apply GlobalTheory.RealPar.KStabLie.kstable_lie <;> assumption)
