import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaHeightAdaptedLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_height_adapted_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → IsHermND σ J →
      IsWittFrame σ J X Y → GlobalTheory.EisLine.IsAdapted σ J X Y L a → ∃ h : GAd σ J → ℝ, IsIwaHtG σ J (col0 X) L a h := by
  first | exact @GlobalTheory.IwHtLine.exists_isIwaHtG | exact GlobalTheory.IwHtLine.exists_isIwaHtG | (intros; apply GlobalTheory.IwHtLine.exists_isIwaHtG <;> assumption)
