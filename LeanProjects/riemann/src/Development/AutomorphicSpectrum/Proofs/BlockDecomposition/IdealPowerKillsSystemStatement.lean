import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerKillsSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_power_kills_system : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] [CompactSpace X] {E : X.Modules}, IsCoherent E → ∀ (D : Subobject E), (D : X.Modules).IsQuasicoherent → ∀ (S : ℕ → Subobject E), (∀ n, (S n : X.Modules).IsQuasicoherent) → ∀ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V → ∀ x ∈ secs D V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V) → ∃ m : ℕ, ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ (powIdeal J₀ m).ideal U → ∀ x ∈ secs D U, a • x ∈ secs (S n) U := by
  first | exact @GlobalTheory.CompanionTheory.GE.Globalize.exists_uniform_pow_kills | exact GlobalTheory.CompanionTheory.GE.Globalize.exists_uniform_pow_kills | (intros; apply GlobalTheory.CompanionTheory.GE.Globalize.exists_uniform_pow_kills <;> assumption)
