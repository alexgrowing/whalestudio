import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointPrescribedFrameImages
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAdelicPoint_prescribed_frameImages : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (C' D' : Matrix (Fin n) (Fin j) (AF F ⊗[F] E)) (Z' : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)), cT (sigR (AF F) σ) C' * adMat F J * C' = 0 → cT (sigR (AF F) σ) D' * adMat F J * D' = 0 → cT (sigR (AF F) σ) C' * adMat F J * D' = 1 → cT (sigR (AF F) σ) C' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) D' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) Z' * adMat F J * Z' = adMat F J₀ → ∃ g : GAd σ J, (matHom _ σ J g).1 * adMat F C = C' ∧ (matHom _ σ J g).1 * adMat F Z = Z' ∧ (matHom _ σ J g).1 * adMat F D = D' := by
  first | exact @GlobalTheory.SphEis.ColImg.exists_point_images | exact GlobalTheory.SphEis.ColImg.exists_point_images | (intros; apply GlobalTheory.SphEis.ColImg.exists_point_images <;> assumption)
