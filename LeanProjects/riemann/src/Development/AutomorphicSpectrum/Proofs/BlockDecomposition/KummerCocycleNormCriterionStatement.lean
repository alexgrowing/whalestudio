import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCocycleNormCriterion
import GroundTheory.ProfiniteCohomology.LocalTateDuality.KummerCup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cocycle_norm_criterion : ∀ {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (N : ℕ), 0 < N → ∀ ζ : Ω, IsPrimitiveRoot ζ N → ∀ c0 : (Ω ≃ₐ[K] Ω) → ZMod N, (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ ^ (c0 g).val) → ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N), IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) → ∀ U : Kˣ, (∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K)) → ∀ (T : Ω) (κ : (Ω ≃ₐ[K] Ω) → ZMod N), T ^ N = algebraMap K Ω (U : K) → (∀ g : Ω ≃ₐ[K] Ω, g T = ζ ^ (κ g).val * T) → ∃ c : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant c ∧ ∀ g h : Ω ≃ₐ[K] Ω, c0 g * c h - c (g * h) + c g = κ g * Multiplicative.toAdd (ψ h) := by
  first | exact @GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary | exact GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary | (intros; apply GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary <;> assumption)
