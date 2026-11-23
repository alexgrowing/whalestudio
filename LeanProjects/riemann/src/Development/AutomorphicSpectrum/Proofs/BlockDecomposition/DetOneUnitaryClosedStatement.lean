import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOneUnitaryClosed
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_one_unitary_closed : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {K : Type} [NontriviallyNormedField K] [Algebra F K], IsClosed {x : HA K σ J | ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1} := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.isClosed_det_eq_one | exact GlobalTheory.CompanionTheory.SaGen.isClosed_det_eq_one | (intros; apply GlobalTheory.CompanionTheory.SaGen.isClosed_det_eq_one <;> assumption)
