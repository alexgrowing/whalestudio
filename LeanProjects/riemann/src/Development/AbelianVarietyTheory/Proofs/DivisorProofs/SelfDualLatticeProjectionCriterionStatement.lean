import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeProjectionCriterion
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
theorem _root_.GlobalTheory.T.self_dual_lattice_projection_criterion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n m r : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ L₀ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L₀ → (∀ v, IsSelfDualAt σ J L₀ v) → (∀ (K : Submodule E (Fin n → E)) (y : Fin n → E), (∀ z ∈ L₀, z ∈ K → hE σ J z y ∈ (algebraMap (𝓞 E) E).range) →
        ∃ z ∈ L₀, ∀ x ∈ K, hE σ J x z = hE σ J x y) →
    ∀ (X Y : Matrix (Fin n) (Fin r) E) (I : Matrix (Fin n) (Fin m) E) (Q : Matrix (Fin m) (Fin n) E),
      cT (σ : E →+* E) X * J * X = 0 → cT (σ : E →+* E) X * J * I = 0 → Q * X = 0 → Q * I = 1 →
      (cT (σ : E →+* E) I * J * I).det ≠ 0 → (cT (σ : E →+* E) I * J * I) * Q = cT (σ : E →+* E) I * J →
      X * (cT (σ : E →+* E) Y * J) + I * Q + Y * (cT (σ : E →+* E) X * J) = 1 →
      ∃ L₀' : Submodule (𝓞 E) (Fin m → E), Submodule.IsLattice E L₀' ∧
        ∀ v, IsSelfDualAt σ (cT (σ : E →+* E) I * J * I) L₀' v := by
  first | exact @GlobalTheory.HypAdapt.Cmpl.exists_selfDual_complement | exact GlobalTheory.HypAdapt.Cmpl.exists_selfDual_complement | (intros; apply GlobalTheory.HypAdapt.Cmpl.exists_selfDual_complement <;> assumption)
