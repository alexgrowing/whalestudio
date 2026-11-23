import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLatticeAdaptedBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittFrame_lattice_adapted_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1 + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → IsHermND σ J → IsWittFrame σ J X Y →
    GlobalTheory.EisLine.IsAdapted σ J X Y L a →
    ∃ (m : ℕ) (ι : (Fin m → E) →ₗ[E] (Fin n → E)) (J₀ : Matrix (Fin m) (Fin m) E)
      (X₀ Y₀ : Matrix (Fin m) (Fin (r + 1)) E) (L₀ : Submodule (𝓞 E) (Fin m → E)) (a₀ : GL (Fin m) (AF F ⊗[F] E)),
      m + 2 = n ∧ IsHermND σ J₀ ∧ IsWittFrame σ J₀ X₀ Y₀ ∧ GlobalTheory.EisLine.IsAdapted σ J₀ X₀ Y₀ L₀ a₀ ∧
      (∀ u v, hE σ J₀ u v = hE σ J (ι u) (ι v)) ∧
      (∀ z, hE σ J (GlobalTheory.EisMidHt.firstColumn X) z = 0 → hE σ J (GlobalTheory.EisMidHt.firstColumn Y) z = 0 → ∃ u, ι u = z) ∧
      ∀ u, GlobalTheory.EisMidHt.ht L₀ a₀ (GlobalTheory.EisMidHt.adVec F u) = GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (ι u)) := by
  first | exact @GlobalTheory.EisRestrict.restrict_adapted | exact GlobalTheory.EisRestrict.restrict_adapted | (intros; apply GlobalTheory.EisRestrict.restrict_adapted <;> assumption)
