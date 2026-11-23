import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → (consCol x B).det ≠ 0 ∧ (∃! e : Hstab R σ J x ≃* HA R σ J', ∀ g : Hstab R σ J x, FrameRelR R σ J J' B (g : HA R σ J) (e g)) ∧ ∀ e : Hstab R σ J x ≃* HA R σ J', (∀ g : Hstab R σ J x, FrameRelR R σ J J' B (g : HA R σ J) (e g)) → Continuous e ∧ Continuous e.symm := by
  first | exact @GlobalTheory.FrameStep.frameStep | exact GlobalTheory.FrameStep.frameStep | (intros; apply GlobalTheory.FrameStep.frameStep <;> assumption)
