import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealMatrixMemBesselUnipotentOfFrame
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementG
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realMatrix_mem_besselUnipotent_of_frame : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {k r : ℕ} (σ : K →+* ℂ) (Φ : V → Fin (2 * r + k + 1) → ℂ),
    GlobalTheory.DegVol.IsReal H k r σ Φ → ∀ (e f : Fin r → V) (ρ ρ' : Fin r → ℂ), (∀ a, ρ a ≠ 0) → (∀ a, ρ' a ≠ 0) →
    (∀ a, Φ (e a) = ρ a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) →
    (∀ a, Φ (f a) = ρ' a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)) →
    (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) →
    ∀ m : V →ₗ[K] V, (∀ x y, H.B (m x) (m y) = H.B x y) →
    (∀ a, m (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) →
    (∀ y, (∀ a, H.B (e a) y = 0) → m y - y ∈ Submodule.span K (Set.range e)) →
    ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (∀ y, n *ᵥ Φ y = Φ (m y)) →
    n ∈ Formalism.QuantumDeterminants.Nset k r := by
  first | exact @GlobalTheory.DegVol.FrameUnip.mem_Nset | exact GlobalTheory.DegVol.FrameUnip.mem_Nset | (intros; apply GlobalTheory.DegVol.FrameUnip.mem_Nset <;> assumption)
