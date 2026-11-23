import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenRowVectorOrbitCompactOpenGL
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_rowVector_orbit_compactOpen_GL : ∀ {F : Type} [NormedField F] {n : ℕ} (B : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B : Set (GL (Fin n) F)) → ∀ r₀ : Fin n → F, r₀ ≠ 0 → IsClopen {r : Fin n → F | ∃ b ∈ B, r = r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)} := by
  first | exact @GlobalTheory.JSW.Orbit.isClopen_orbit | exact GlobalTheory.JSW.Orbit.isClopen_orbit | (intros; apply GlobalTheory.JSW.Orbit.isClopen_orbit <;> assumption)
