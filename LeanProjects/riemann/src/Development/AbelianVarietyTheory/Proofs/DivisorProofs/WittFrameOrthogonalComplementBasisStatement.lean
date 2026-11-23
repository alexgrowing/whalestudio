import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameOrthogonalComplementBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdaptedLatticeFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_orthogonal_complement_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∃ (m : ℕ) (I : Matrix (Fin n) (Fin m) E) (Q : Matrix (Fin m) (Fin n) E), m + 2 * r = n ∧
      cT (σ : E →+* E) I * J * X = 0 ∧ cT (σ : E →+* E) I * J * Y = 0 ∧
      cT (σ : E →+* E) X * J * I = 0 ∧ cT (σ : E →+* E) Y * J * I = 0 ∧
      Q * X = 0 ∧ Q * Y = 0 ∧ Q * I = 1 ∧ (cT (σ : E →+* E) I * J * I) * Q = cT (σ : E →+* E) I * J ∧
      X * (cT (σ : E →+* E) Y * J) + I * Q + Y * (cT (σ : E →+* E) X * J) = 1 ∧
      IsHermND σ (cT (σ : E →+* E) I * J * I) := by
  first | exact @GlobalTheory.WittCompl.exists_complement_data | exact GlobalTheory.WittCompl.exists_complement_data | (intros; apply GlobalTheory.WittCompl.exists_complement_data <;> assumption)
