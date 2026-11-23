import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryHermFrameUnipotent
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementG
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_hermFrame_unipotent : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {r : ℕ} (e f e' f' : Fin r → V) (z z' : V),
    (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (f a) (f b) = 0) →
    (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, H.B (e a) z = 0) → (∀ a, H.B (f a) z = 0) → H.B z z ≠ 0 →
    (∀ a b, H.B (e' a) (e' b) = 0) → (∀ a b, H.B (f' a) (f' b) = 0) →
    (∀ a b, H.B (e' a) (f' b) = if a = b then 1 else 0) →
    (∀ a, H.B (e' a) z' = 0) → (∀ a, H.B (f' a) z' = 0) →
    (∀ a, e' a - e a ∈ Submodule.span K (e '' {b | b < a})) →
    z' - z ∈ Submodule.span K (Set.range e) →
    ∃ m : V ≃ₗ[K] V, (∀ x y, H.B (m x) (m y) = H.B x y) ∧ (∀ a, m (e' a) = e a) ∧ (∀ a, m (f' a) = f a) ∧
      m z' = z ∧ (∀ a, m (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) ∧
      (∀ y, (∀ a, H.B (e a) y = 0) → m y - y ∈ Submodule.span K (Set.range e)) ∧
      (∀ a, m.symm (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) ∧
      (∀ y, (∀ a, H.B (e a) y = 0) → m.symm y - y ∈ Submodule.span K (Set.range e)) := by
  first | exact @GlobalTheory.RatIsoFrame.exists_isometry_frame_unipotent | exact GlobalTheory.RatIsoFrame.exists_isometry_frame_unipotent | (intros; apply GlobalTheory.RatIsoFrame.exists_isometry_frame_unipotent <;> assumption)
