import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockMinorProductEqSignDualWeylExtremalVector
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockMinorProduct_eq_sign_dualWeylExtremalVector : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → ∃ s : ℤˣ, ∀ x, harmFn m w B (w.delta m) x = ((s : ℤ) : ℂ) * coefFn (RingHom.id ℂ) w.lam (ten fun τ => extremal ℂ n (w.lam τ)) (B⁻¹ * x) := by
  first | exact @GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta | exact GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta | (intros; apply GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta <;> assumption)
