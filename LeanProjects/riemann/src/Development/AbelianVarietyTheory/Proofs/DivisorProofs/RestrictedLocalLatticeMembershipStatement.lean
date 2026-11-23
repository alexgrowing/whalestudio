import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedLocalLatticeMembership
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
theorem _root_.GlobalTheory.T.restricted_local_lattice_membership : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), GlobalTheory.EisLine.IsAdapted σ J X Y L a →
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (u : Fin (dim σ J X Y) → Fv F v ⊗[F] E),
      u ∈ latLoc F (L0 σ J X Y L) v ↔ (P σ J X Y).map (inclR (F := F) (Fv F v)) *ᵥ u ∈ latLoc F L v := by
  first | exact @GlobalTheory.EisRestrict.mem_localLattice_restricted_iff | exact GlobalTheory.EisRestrict.mem_localLattice_restricted_iff | (intros; apply GlobalTheory.EisRestrict.mem_localLattice_restricted_iff <;> assumption)
