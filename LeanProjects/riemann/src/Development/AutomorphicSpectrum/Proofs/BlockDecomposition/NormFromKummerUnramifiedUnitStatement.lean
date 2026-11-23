import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFromKummerUnramifiedUnit
import GroundTheory.LocalFields.MainTheorem
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_from_kummer_unramified_unit : ∀ {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (N : ℕ), N ≠ 0 → ∀ ξ : Ω, IsPrimitiveRoot ξ (Nat.card 𝓀[K] ^ N - 1) → ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N), IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) → (∀ g : Ω ≃ₐ[K] Ω, g ξ = ξ → ψ g = 1) → ∀ U : Kˣ, GroundTheory.LocalField.ord (U : K) = 0 → ∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K) := by
  first | exact @GlobalTheory.CompanionTheory.LocalField.exists_norm_fixedField_ker_eq_unit | exact GlobalTheory.CompanionTheory.LocalField.exists_norm_fixedField_ker_eq_unit | (intros; apply GlobalTheory.CompanionTheory.LocalField.exists_norm_fixedField_ker_eq_unit <;> assumption)
