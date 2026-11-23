import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedLatticeSplit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_lattice_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), GlobalTheory.EisLine.IsAdapted σ J X Y L a →
    ∀ z ∈ L0 σ J X Y L, ∀ i, ((Formalism.UG.cT (σ : E →+* E) (Y0 σ J X Y) * J0 σ J X Y) *ᵥ z) i • (X0 σ J X Y)ᵀ i ∈ L0 σ J X Y L ∧
      ((Formalism.UG.cT (σ : E →+* E) (X0 σ J X Y) * J0 σ J X Y) *ᵥ z) i • (Y0 σ J X Y)ᵀ i ∈ L0 σ J X Y L := by
  first | exact @GlobalTheory.EisRestrictSplit.restrictedLattice_split | exact GlobalTheory.EisRestrictSplit.restrictedLattice_split | (intros; apply GlobalTheory.EisRestrictSplit.restrictedLattice_split <;> assumption)
