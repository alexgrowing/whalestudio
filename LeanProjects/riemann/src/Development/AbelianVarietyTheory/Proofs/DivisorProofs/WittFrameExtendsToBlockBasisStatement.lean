import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameExtendsToBlockBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_extends_to_block_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • J.map σ) Xf Yf →
    ∃ (n₀ : ℕ) (Z₀ : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin n) E),
      n₀ + (r₀ + r₀) = n ∧
      Q * Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) = 1 ∧ Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) * Q = 1 ∧
      (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf))ᵀ * J * (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf)).map σ =
        Matrix.fromBlocks (Z₀ᵀ * J * Z₀.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) ∧
      (Z₀ᵀ * J * Z₀.map σ).det ≠ 0 ∧ (∀ i j, σ ((Z₀ᵀ * J * Z₀.map σ) j i) = (Z₀ᵀ * J * Z₀.map σ) i j) ∧
      Formalism.UG.cT (σ : E →+* E) Xf * ((1 : E) • J.map σ) * Z₀ = 0 ∧ Formalism.UG.cT (σ : E →+* E) Yf * ((1 : E) • J.map σ) * Z₀ = 0 := by
  first | exact @GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis | exact GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis | (intros; apply GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis <;> assumption)
