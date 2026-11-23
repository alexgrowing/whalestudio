import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlaceRelativeNormLeLocalSizePow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePlace_relativeNorm_le_localSize_pow : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (y : D.host.E), ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F y)‖₊ ≤ GlobalTheory.AdelicU.absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] y) ^ Module.finrank D.host.F D.host.E := by
  first | exact @GlobalTheory.NormFin.normFin_le | exact GlobalTheory.NormFin.normFin_le | (intros; apply GlobalTheory.NormFin.normFin_le <;> assumption)
