import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingIntegrandBoundedSchwartz
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnfoldingIntegrand_boundedSchwartz : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (n' c' n c : ℕ) (psi : E → K) (D N : ℕ) (Psi : Loc.SF E K (n' + c') (n + c)), N ≤ D → CharTo P D psi → HomBdd P N Psi → ∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E), FunBdd P N (integrand psi Psi xj) ∧ ∀ t : Loc.FC n' c' n c → E, Psi (Loc.xx1 xj t) ≠ 0 → IntAt P ((qOf P : E) ^ N * Loc.chArg (Loc.xx1 xj t)) := by
  first | exact @GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd | exact GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd | (intros; apply GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd <;> assumption)
