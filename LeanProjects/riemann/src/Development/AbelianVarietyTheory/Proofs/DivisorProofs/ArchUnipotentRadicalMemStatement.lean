import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchUnipotentRadicalMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.TorFin
open GlobalTheory.Orb (archMat)
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_unipotent_radical_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x : Fin n → E) (w : InfinitePlace F) (τ : EmbOver E w) (y : GArch σ J w), archMat σ J τ y - 1 ∈ nilRad (J.map τ.1) (fun i => τ.1 (x i)) → embArch σ J w y ∈ unipRad σ J (Matrix.of fun i (_ : Fin 1) => x i) := by
  first | exact @GlobalTheory.TorFin.embArch_mem_unipRad_of_nilRad | exact GlobalTheory.TorFin.embArch_mem_unipRad_of_nilRad | (intros; apply GlobalTheory.TorFin.embArch_mem_unipRad_of_nilRad <;> assumption)
