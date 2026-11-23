import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldIso_selfDual_and_periodLattices_agree : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → (∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → StandardLatticesGL3.SD D (s.lat N)) ∧ ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : VCx X.Tau a b), z ∈ lam (ambOf s B χ cD) N N' ↔ (fun τ => z (s.iT.symm τ)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N') := by
  first | exact @GlobalTheory.PeriodTransport.seam_lattices | exact GlobalTheory.PeriodTransport.seam_lattices | (intros; apply GlobalTheory.PeriodTransport.seam_lattices <;> assumption)
