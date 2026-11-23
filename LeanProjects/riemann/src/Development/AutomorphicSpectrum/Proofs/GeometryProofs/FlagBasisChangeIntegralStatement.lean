import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisChangeIntegral
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_basis_change_integral : ∀ (K : Type) [Field K] (R : Subring K) [IsLocalRing R] (r : ℕ) (g : Fin r → Fin r → K), (∀ k : Fin r, ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧ (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧ ∀ l, D l ∈ flagStep K g ((k : ℕ) + 1)) → ∃ P : Matrix (Fin r) (Fin r) K, (∀ a b, P a b ∈ R) ∧ P.det ≠ 0 ∧ P.det⁻¹ ∈ R ∧ ∀ i, flagStep K (fun k a => P a k) i = flagStep K g i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted <;> assumption)
