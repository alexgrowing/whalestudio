import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticFormOrbitRationalVectorEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_quadratic_form_orbit_rational_vector_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (a : F), hE σ J (x 0) (x 0) = algebraMap F E a → ∀ g : HA R σ J, qR R σ J ((g • ratTup (F := F) R x) 0) = algebraMap F R a := by
  first | exact @GlobalTheory.GaugeEx.OrbitQuadric.qR_orbit | exact GlobalTheory.GaugeEx.OrbitQuadric.qR_orbit | (intros; apply GlobalTheory.GaugeEx.OrbitQuadric.qR_orbit <;> assumption)
